//! Manage global state and thread-local workspaces.

use byteorder::{ReadBytesExt, WriteBytesExt};
use std::borrow::Cow;
use std::hash::Hash;
use std::io::{Read, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Once, OnceLock, RwLock, RwLockWriteGuard};
use std::thread::LocalKey;
use std::{
    cell::{Cell, RefCell},
    collections::hash_map::Entry,
    ops::{Deref, DerefMut},
};

use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use append_only_vec::AppendOnlyVec;
use byteorder::LittleEndian;
use smartstring::alias::String;

use crate::atom::{
    AtomCore, AtomView, DerivativeFunction, EvaluationInfo, NamespacedSymbol,
    NormalizationFunction, SeriesExpansionFunction, SymbolAttribute, SymbolBuilder, UserData,
    UserDataKey,
};
use crate::coefficient::CoefficientView;
use crate::domains::finite_field::Zp64;
use crate::poly::PolyVariable;
use crate::printer::PrintFunction;
use crate::warn;
use crate::{
    LicenseManager,
    atom::{Atom, Symbol},
    coefficient::Coefficient,
    domains::{
        finite_field::FiniteFieldCore,
        float::{Complex, Float, Real},
    },
};

pub(crate) const SYMBOLICA_MAGIC: u32 = 0x37871367;
pub(crate) const EXPORT_FORMAT_VERSION: u16 = 5;
pub(crate) const SUPPORTED_IMPORT_VERSIONS: &[u16] = &[4, 5];
pub(crate) const FULL_STATE_EXPORT_FLAG: u8 = 1;

/// An id for a given finite field in a registry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FiniteFieldIndex(pub(crate) usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct VariableListIndex(pub(crate) usize);

/// A mapping from one state to the other. Used during importing
/// for merging a state on file with the current state.
#[derive(Default)]
pub struct StateMap {
    pub(crate) symbols: HashMap<u32, Symbol>,
    pub(crate) finite_fields: HashMap<FiniteFieldIndex, FiniteFieldIndex>,
    pub(crate) variables_lists: HashMap<u64, Arc<Vec<PolyVariable>>>,
}

///Trait for anything that contains a StateMap
pub trait HasStateMap {
    fn get_state_map(&self) -> &StateMap;
}

impl HasStateMap for StateMap {
    fn get_state_map(&self) -> &StateMap {
        self
    }
}

impl StateMap {
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty() && self.finite_fields.is_empty() && self.variables_lists.is_empty()
    }
}

struct ImportedSymbol {
    index: u32,
    name: std::string::String,
    namespace: std::string::String,
    attributes: Vec<SymbolAttribute>,
    tags: Vec<std::string::String>,
    user_data: UserData,
    aliases: Vec<std::string::String>,
    is_exportable: bool,
}

enum ImportedPolyVariable {
    Symbol(u32),
    Temporary(usize),
    Function(u32, Atom),
    Power(Atom),
}

struct ImportedVariableList {
    index: u64,
    variables: Vec<ImportedPolyVariable>,
}

#[derive(Default)]
struct StateDependencies {
    symbols: HashSet<u32>,
    variable_lists: HashSet<u64>,
}

impl StateDependencies {
    fn add_atom(&mut self, atom: AtomView<'_>) {
        self.symbols.extend(
            atom.get_all_symbols(true)
                .into_iter()
                .map(|symbol| symbol.get_id()),
        );
        self.add_atom_variable_lists(atom);
    }

    fn add_atom_variable_lists(&mut self, atom: AtomView<'_>) {
        match atom {
            AtomView::Num(number) => {
                if let CoefficientView::RationalPolynomial(polynomial) = number.get_coeff_view() {
                    self.variable_lists.insert(polynomial.variable_list_index());
                }
            }
            AtomView::Var(_) => {}
            AtomView::Fun(function) => {
                for argument in function {
                    self.add_atom_variable_lists(argument);
                }
            }
            AtomView::Pow(power) => {
                let (base, exponent) = power.get_base_exp();
                self.add_atom_variable_lists(base);
                self.add_atom_variable_lists(exponent);
            }
            AtomView::Mul(product) => {
                for factor in product {
                    self.add_atom_variable_lists(factor);
                }
            }
            AtomView::Add(sum) => {
                for term in sum {
                    self.add_atom_variable_lists(term);
                }
            }
        }
    }

    fn add_user_data(&mut self, data: &UserData) {
        match data {
            UserData::None
            | UserData::Integer(_)
            | UserData::String(_)
            | UserData::Serialized(_) => {}
            UserData::Atom(atom) => self.add_atom(atom.as_view()),
            UserData::List(list) => {
                for item in list {
                    self.add_user_data(item);
                }
            }
            UserData::Map(map) => {
                for (key, value) in map {
                    if let UserDataKey::Atom(atom) = key {
                        self.add_atom(atom.as_view());
                    }
                    self.add_user_data(value);
                }
            }
        }
    }

    fn add_imported_variable(&mut self, variable: &ImportedPolyVariable) {
        match variable {
            ImportedPolyVariable::Symbol(symbol) => {
                self.symbols.insert(*symbol);
            }
            ImportedPolyVariable::Temporary(_) => {}
            ImportedPolyVariable::Function(symbol, atom) => {
                self.symbols.insert(*symbol);
                self.add_atom(atom.as_view());
            }
            ImportedPolyVariable::Power(atom) => self.add_atom(atom.as_view()),
        }
    }
}

fn collect_variable_symbols(variable: &PolyVariable, symbols: &mut HashSet<Symbol>) {
    match variable {
        PolyVariable::Symbol(symbol) => {
            symbols.insert(*symbol);
        }
        PolyVariable::Temporary(_) => {}
        PolyVariable::Function(symbol, atom) => {
            symbols.insert(*symbol);
            symbols.extend(atom.get_all_symbols(true));
        }
        PolyVariable::Power(atom) => symbols.extend(atom.get_all_symbols(true)),
    }
}

fn collect_export_symbols(
    initial: &HashSet<Symbol>,
    initial_variable_lists: &HashSet<u64>,
) -> Result<HashSet<Symbol>, std::io::Error> {
    fn visit(
        symbol: Symbol,
        visiting: &mut HashSet<u32>,
        visited: &mut HashSet<u32>,
        output: &mut HashSet<Symbol>,
        variable_lists: &mut HashSet<u64>,
    ) -> Result<(), std::io::Error> {
        let id = symbol.get_id();
        if visited.contains(&id) {
            return Ok(());
        }
        if !visiting.insert(id) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("Cyclic symbol user data involving {}", symbol.get_name()),
            ));
        }

        let mut dependencies = HashSet::default();
        symbol.get_data().get_symbols(&mut dependencies);
        let mut state_dependencies = StateDependencies::default();
        state_dependencies.add_user_data(symbol.get_data());
        variable_lists.extend(state_dependencies.variable_lists);
        for dependency in dependencies {
            visit(dependency, visiting, visited, output, variable_lists)?;
        }

        visiting.remove(&id);
        visited.insert(id);
        output.insert(symbol);
        Ok(())
    }

    let mut output = HashSet::default();
    let mut visiting = HashSet::default();
    let mut visited = HashSet::default();
    let mut pending_variable_lists = initial_variable_lists.clone();
    for symbol in initial {
        visit(
            *symbol,
            &mut visiting,
            &mut visited,
            &mut output,
            &mut pending_variable_lists,
        )?;
    }

    let mut visited_variable_lists = HashSet::default();
    while let Some(index) = pending_variable_lists
        .iter()
        .find(|index| !visited_variable_lists.contains(*index))
        .copied()
    {
        if index as usize >= VARIABLE_LISTS.len() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("Expression references missing variable list {index}"),
            ));
        }
        let variables = &VARIABLE_LISTS[index as usize];
        visited_variable_lists.insert(index);

        let mut symbols = HashSet::default();
        let mut state_dependencies = StateDependencies::default();
        for variable in variables.iter() {
            collect_variable_symbols(variable, &mut symbols);
            match variable {
                PolyVariable::Symbol(_) | PolyVariable::Temporary(_) => {}
                PolyVariable::Function(_, atom) | PolyVariable::Power(atom) => {
                    state_dependencies.add_atom(atom.as_view());
                }
            }
        }
        pending_variable_lists.extend(state_dependencies.variable_lists);
        for symbol in symbols {
            visit(
                symbol,
                &mut visiting,
                &mut visited,
                &mut output,
                &mut pending_variable_lists,
            )?;
        }
    }
    Ok(output)
}

fn register_imported_symbol(
    record: ImportedSymbol,
    state_map: &StateMap,
    conflict_fn: Option<&dyn Fn(&str) -> String>,
) -> Result<Symbol, std::io::Error> {
    let ImportedSymbol {
        index: _,
        mut name,
        namespace,
        attributes,
        tags,
        user_data,
        aliases,
        is_exportable,
    } = record;
    let user_data = user_data.rename_symbols(state_map);
    let mut attempted_names = HashSet::default();
    attempted_names.insert(name.clone());

    loop {
        let num_symbols = ID_TO_STR.len();
        match SymbolBuilder::new(NamespacedSymbol {
            symbol: name.clone().into(),
            namespace: namespace.clone().into(),
            file: "".into(),
            line: 0,
        })
        .with_attributes(attributes.clone())
        .with_tags(tags.clone())
        .with_user_data(user_data.clone())
        .with_aliases(aliases.clone())
        .build()
        {
            Ok(symbol) => {
                if !is_exportable && num_symbols != ID_TO_STR.len() {
                    warn!(
                        "Imported symbol {name} was previously defined with user-defined functions, but the imported version does not have any."
                    );
                }
                return Ok(symbol);
            }
            Err(error) => {
                let Some(rename) = conflict_fn else {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!("Symbol conflict: {error}"),
                    ));
                };

                let new_name = rename(&name).to_string();
                let wildcard_level = |value: &str| {
                    value
                        .chars()
                        .rev()
                        .take_while(|character| *character == '_')
                        .count()
                };
                if wildcard_level(&name) != wildcard_level(&new_name) {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!(
                            "Conflict resolver changed the wildcard level of symbol {name} to {new_name}"
                        ),
                    ));
                }
                if !attempted_names.insert(new_name.clone()) {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!(
                            "Conflict resolver produced a repeated name while importing symbol {name}: {new_name}"
                        ),
                    ));
                }
                name = new_name;
            }
        }
    }
}

fn resolve_variable_list(
    record: ImportedVariableList,
    resolved_symbols: &HashMap<u32, Symbol>,
    state_map: &StateMap,
) -> Result<Arc<Vec<PolyVariable>>, std::io::Error> {
    let mut variables = Vec::with_capacity(record.variables.len());
    for variable in record.variables {
        match variable {
            ImportedPolyVariable::Symbol(id) => {
                let symbol = resolved_symbols.get(&id).copied().ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!(
                            "Variable list {} references unresolved symbol id {id}",
                            record.index
                        ),
                    )
                })?;
                variables.push(PolyVariable::Symbol(symbol));
            }
            ImportedPolyVariable::Temporary(value) => {
                variables.push(PolyVariable::Temporary(value));
            }
            ImportedPolyVariable::Function(id, atom) => {
                let symbol = resolved_symbols.get(&id).copied().ok_or_else(|| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!(
                            "Variable list {} references unresolved function id {id}",
                            record.index
                        ),
                    )
                })?;
                variables.push(PolyVariable::Function(
                    symbol,
                    atom.as_view().rename(state_map),
                ));
            }
            ImportedPolyVariable::Power(atom) => {
                variables.push(PolyVariable::Power(atom.as_view().rename(state_map)));
            }
        }
    }
    Ok(Arc::new(variables))
}

pub(crate) struct SymbolData {
    pub(crate) name: String,
    pub(crate) namespace: Cow<'static, str>,
    pub(crate) file: Cow<'static, str>,
    pub(crate) line: usize,
    pub(crate) custom_normalization: Option<NormalizationFunction>,
    pub(crate) custom_print: Option<PrintFunction>,
    pub(crate) custom_derivative: Option<DerivativeFunction>,
    pub(crate) custom_series: Option<Box<SeriesExpansionFunction>>,
    pub(crate) custom_evaluation: Option<EvaluationInfo>,
    pub(crate) custom_function_keys: CustomFunctionDefinitionKeys,
    pub(crate) aliases: Vec<std::string::String>,
    pub(crate) tags: Vec<std::string::String>,
    pub(crate) user_data: UserData,
}

/// Opaque keys used to recognize equivalent custom function definitions.
///
/// Public Rust symbol builders leave these keys empty, preserving the rule that
/// callbacks are registered once. The Python API supplies them so that rerunning
/// a notebook cell with an equivalent callback is idempotent.
#[derive(Default)]
pub(crate) struct CustomFunctionDefinitionKeys {
    pub(crate) normalization: Option<Vec<u8>>,
    pub(crate) print: Option<Vec<u8>>,
    pub(crate) derivative: Option<Vec<u8>>,
    pub(crate) series: Option<Vec<u8>>,
    pub(crate) evaluation: Option<Vec<u8>>,
}

fn custom_function_matches<T>(
    new_function: &Option<T>,
    new_key: &Option<Vec<u8>>,
    existing_function: &Option<T>,
    existing_key: &Option<Vec<u8>>,
) -> bool {
    new_function.is_none()
        || (existing_function.is_some()
            && new_key
                .as_ref()
                .is_some_and(|key| existing_key.as_ref() == Some(key)))
}

fn builtin_constant_evaluation(symbol: Symbol) -> Option<EvaluationInfo> {
    match symbol.get_id() {
        Symbol::E_ID => Some(EvaluationInfo::constant(|_tags, prec| {
            Ok(Complex::new(
                Float::with_val(prec, 1).exp(),
                Float::new(prec),
            ))
        })),
        Symbol::PI_ID => Some(EvaluationInfo::constant(|_tags, prec| {
            Ok(Complex::new(
                Float::with_val(prec, crate::domains::backend::float::Constant::Pi),
                Float::new(prec),
            ))
        })),
        _ => None,
    }
}

impl SymbolData {
    fn default_from_symbol(name: &str) -> Self {
        Self {
            name: format!("symbolica::{}", name).into(),
            file: file!().into(),
            namespace: "symbolica".into(),
            line: line!() as usize,
            custom_normalization: None,
            custom_print: None,
            custom_derivative: None,
            custom_series: None,
            custom_evaluation: None,
            custom_function_keys: CustomFunctionDefinitionKeys::default(),
            aliases: vec![],
            tags: vec![],
            user_data: UserData::None,
        }
    }
}

/// An initializer called when the Symbolica global state is initialized.
/// Use [`initialize!`](crate::initialize) to register state initializers.
pub struct StateInitializer {
    init: fn(),
    name: &'static str,
    dependencies: &'static [&'static str],
}

impl StateInitializer {
    /// Creates a new state initializer with the given initialization function.
    pub const fn new(
        name: &'static str,
        init: fn(),
        dependencies: &'static [&'static str],
    ) -> Self {
        Self {
            init,
            name,
            dependencies,
        }
    }
}

/// An initializer called when the Symbolica global state is initialized.
/// It can be used to register symbols before any other use.
/// If the intialization depends on other initializations, provide
/// the crate names of the dependencies as additional arguments.
///
/// This macro should be called outside of any functions.
///
/// ```ignore
/// use symbolica::prelude::*;
///
/// initialize!(|| {
///     symbol!("your_symbol"; Linear);
/// });
///
/// fn main() { }
/// ```
#[macro_export]
macro_rules! initialize {
    ($init:expr $(, $deps:expr)* $(,)?) => {
        $crate::_inventory::submit! {
            $crate::state::StateInitializer::new(
                env!("CARGO_CRATE_NAME"),
                $init,
                &["symbolica", $($deps),*],
            )
        }
    };
}

#[cfg(not(doctest))]
inventory::submit! {
    StateInitializer::new(
        "symbolica",
        || { },
        &[]
    )
}

inventory::collect!(StateInitializer);

static STATE: OnceLock<RwLock<State>> = OnceLock::new();
static STATE_INITIALIZER: Once = Once::new();
static ID_TO_STR: AppendOnlyVec<(Symbol, SymbolData)> = AppendOnlyVec::new();
static FINITE_FIELDS: AppendOnlyVec<Zp64> = AppendOnlyVec::new();
static VARIABLE_LISTS: AppendOnlyVec<Arc<Vec<PolyVariable>>> = AppendOnlyVec::new();
static SYMBOL_OFFSET: AtomicUsize = AtomicUsize::new(0);

thread_local!(
    /// A thread-local workspace, that stores recyclable atoms.
    static WORKSPACE: Workspace = const { Workspace::new() }
);

thread_local!(
    static RUNNING_STATE_INITIALIZER: Cell<bool> = const { Cell::new(false) }
);

/// A global state, that stores mappings from variable and function names to ids.
pub struct State {
    str_to_id: HashMap<String, Symbol>,
    builtin_symbols: HashSet<String>,
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

impl State {
    pub(crate) const ARG: Symbol = Symbol::raw_fn(
        0, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const COEFF: Symbol = Symbol::raw_fn(
        1, 0, false, false, false, false, false, true, false, false, false,
    );
    pub(crate) const EXP: Symbol = Symbol::raw_fn(
        2, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const LOG: Symbol = Symbol::raw_fn(
        3, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const SIN: Symbol = Symbol::raw_fn(
        4, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const COS: Symbol = Symbol::raw_fn(
        5, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const SQRT: Symbol = Symbol::raw_fn(
        6, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const CONJ: Symbol = Symbol::raw_fn(
        7, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const ABS: Symbol = Symbol::raw_fn(
        8, 0, false, false, false, false, false, false, true, false, true,
    );
    pub(crate) const IF: Symbol = Symbol::raw_fn(
        9, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const DERIVATIVE: Symbol = Symbol::raw_fn(
        10, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const E: Symbol = Symbol::raw_fn(
        11, 0, false, false, false, false, false, true, true, false, true,
    );
    pub(crate) const PI: Symbol = Symbol::raw_fn(
        12, 0, false, false, false, false, false, true, true, false, true,
    );
    pub(crate) const SEP: Symbol = Symbol::raw_fn(
        13, 0, false, false, false, false, false, true, true, true, true,
    );
    pub(crate) const OPT: Symbol = Symbol::raw_fn(
        14, 0, false, false, false, false, false, false, false, false, false,
    );
    pub(crate) const ALT: Symbol = Symbol::raw_fn(
        15, 0, false, false, false, false, false, false, false, false, false,
    );

    /// The list of built-in symbols.
    pub const BUILTIN_SYMBOL_NAMES: [&'static str; 16] = [
        "arg",
        "coeff",
        "exp",
        "log",
        "sin",
        "cos",
        "sqrt",
        "conj",
        "abs",
        "if",
        "der",
        Symbol::E_STR,
        Symbol::PI_STR,
        Symbol::SEP_STR,
        "opt",
        "alt",
    ];

    /// The list of built-in symbol names and their aliases.
    pub const BUILTIN_NAMES_AND_ALIASES: [&'static str; 18] = [
        "arg",
        "coeff",
        "exp",
        "log",
        "sin",
        "cos",
        "sqrt",
        "conj",
        "abs",
        "if",
        "der",
        Symbol::E_STR,
        Symbol::PI_STR,
        Symbol::SEP_STR,
        "opt",
        "alt",
        "euler_e",
        "pi",
    ];

    /// The list of built-in symbols.
    pub const BUILTIN_SYMBOLS: [Symbol; 16] = [
        Self::ARG,
        Self::COEFF,
        Self::EXP,
        Self::LOG,
        Self::SIN,
        Self::COS,
        Self::SQRT,
        Self::CONJ,
        Self::ABS,
        Self::IF,
        Self::DERIVATIVE,
        Self::E,
        Self::PI,
        Self::SEP,
        Self::OPT,
        Self::ALT,
    ];

    pub(crate) fn is_builtin_name<S: AsRef<str>>(&self, str: S) -> bool {
        self.builtin_symbols.contains(str.as_ref())
    }

    /// Returns `true` iff the given string is the name of a built-in symbol.
    pub fn is_builtin<S: AsRef<str>>(str: S) -> bool {
        Self::get_global_state()
            .read()
            .unwrap()
            .builtin_symbols
            .contains(str.as_ref())
    }

    fn initialize_builtin_symbols(&mut self) {
        let offset = SYMBOL_OFFSET.load(Ordering::Relaxed);

        for (name, symbol) in Self::BUILTIN_SYMBOL_NAMES.iter().zip(Self::BUILTIN_SYMBOLS) {
            let mut data = SymbolData::default_from_symbol(name);
            data.custom_evaluation = builtin_constant_evaluation(symbol);

            self.builtin_symbols.insert((*name).into());
            if symbol == Self::E {
                data.aliases = vec!["symbolica::euler_e".to_owned()];
                self.builtin_symbols.insert("euler_e".into());
            } else if symbol == Self::PI {
                data.aliases = vec!["symbolica::pi".to_owned()];
                self.builtin_symbols.insert("pi".into());
            }

            let id = ID_TO_STR.push((symbol, data)) - offset;
            assert_eq!(symbol.get_id() as usize, id);

            let data = &ID_TO_STR[id + offset].1;
            self.str_to_id.insert(data.name.clone(), symbol);

            for alias in &data.aliases {
                self.str_to_id.insert(alias.clone().into(), symbol);
            }
        }
    }

    fn new() -> State {
        let mut state = State {
            str_to_id: HashMap::new(),
            builtin_symbols: HashSet::new(),
        };

        state.initialize_builtin_symbols();

        state
    }

    /// Initializes the state by running all registered state initializers in a topological order.
    /// This function is re-entry safe.
    fn initialize_state() {
        struct ReentryGuard;

        impl ReentryGuard {
            fn enter(running: &'static LocalKey<Cell<bool>>) -> Self {
                running.with(|running| {
                    assert!(
                        !running.replace(true),
                        "nested state initializer execution is not supported"
                    );
                });

                Self
            }
        }

        impl Drop for ReentryGuard {
            fn drop(&mut self) {
                RUNNING_STATE_INITIALIZER.with(|running| running.set(false));
            }
        }

        STATE.get_or_init(|| RwLock::new(State::new()));

        if RUNNING_STATE_INITIALIZER.with(|running| running.get()) {
            return;
        }

        let mut initializing = false;
        STATE_INITIALIZER.call_once(|| {
            let _guard = ReentryGuard::enter(&RUNNING_STATE_INITIALIZER);
            initializing = true;

            #[cfg(test)]
            {
                STATE.get().unwrap().write().unwrap().initialize_test();
            }

            // topologically sort the initializers based on their dependencies, and run them in order
            let mut initializers: Vec<_> =
                inventory::iter::<StateInitializer>.into_iter().collect();
            initializers.sort_by_key(|initializer| initializer.name);

            let mut initializers_by_name = HashMap::with_capacity(initializers.len());
            for initializer in &initializers {
                if initializers_by_name
                    .insert(initializer.name, *initializer)
                    .is_some()
                {
                    panic!(
                        "Multiple state initializers registered for crate `{}`",
                        initializer.name
                    );
                }
            }

            #[derive(Clone, Copy, PartialEq, Eq)]
            enum VisitState {
                Visiting,
                Visited,
            }

            // depth first visit to sort the initializers based on their dependencies
            fn visit_initializer<'a>(
                current: &'a StateInitializer,
                initializer: &HashMap<&'static str, &'a StateInitializer>,
                visit_state: &mut HashMap<&'static str, VisitState>,
                ordered_initializers: &mut Vec<&'a StateInitializer>,
            ) {
                match visit_state.get(current.name) {
                    Some(VisitState::Visited) => return,
                    Some(VisitState::Visiting) => {
                        panic!(
                            "Cyclic state initializer dependency involving crate `{}`",
                            current.name
                        );
                    }
                    None => {}
                }

                visit_state.insert(current.name, VisitState::Visiting);

                for dependency in current.dependencies {
                    let dependency_initializer = initializer.get(dependency).unwrap_or_else(|| {
                        panic!(
                            "State initializer for crate `{}` depends on missing crate `{}`",
                            current.name, dependency
                        )
                    });
                    visit_initializer(
                        dependency_initializer,
                        initializer,
                        visit_state,
                        ordered_initializers,
                    );
                }

                visit_state.insert(current.name, VisitState::Visited);
                ordered_initializers.push(current);
            }

            let mut ordered_initializers = Vec::with_capacity(initializers.len());
            let mut visit_state = HashMap::with_capacity(initializers.len());
            for initializer in &initializers {
                visit_initializer(
                    initializer,
                    &initializers_by_name,
                    &mut visit_state,
                    &mut ordered_initializers,
                );
            }

            for initializer in ordered_initializers {
                (initializer.init)();
            }
        });

        if !initializing {
            LicenseManager::check();
        }
    }

    /// Get the global state.
    #[inline]
    pub(crate) fn get_global_state() -> &'static RwLock<State> {
        Self::initialize_state();
        STATE.get().unwrap()
    }

    /// Initialize the global state for testing purposes by allocating
    /// variables and functions with the names v0, ..., v29, f0, ..., f29,
    /// that can be used in concurrently run unit tests without interference.
    #[cfg(test)]
    fn initialize_test(&mut self) {
        use crate::{atom::SymbolAttribute, wrap_symbol};

        for i in 0..30 {
            let _ = self.get_symbol(wrap_symbol!(format!("symbolica::v{}", i)));
        }
        for i in 0..30 {
            let _ = self.get_symbol(wrap_symbol!(format!("symbolica::f{}", i)));
        }
        for i in 0..5 {
            let _ = self.get_symbol_with_attributes(
                wrap_symbol!(format!("symbolica::fs{}", i)),
                &[SymbolAttribute::Symmetric],
                None,
                None,
                None,
                None,
                None,
                CustomFunctionDefinitionKeys::default(),
                vec![],
                vec![],
                None,
            );
        }
        for i in 0..5 {
            let _ = self.get_symbol_with_attributes(
                wrap_symbol!(format!("symbolica::fc{}", i)),
                &[SymbolAttribute::Cyclesymmetric],
                None,
                None,
                None,
                None,
                None,
                CustomFunctionDefinitionKeys::default(),
                vec![],
                vec![],
                None,
            );
        }
        for i in 0..5 {
            let _ = self.get_symbol_with_attributes(
                wrap_symbol!(format!("symbolica::fa{}", i)),
                &[SymbolAttribute::Antisymmetric],
                None,
                None,
                None,
                None,
                None,
                CustomFunctionDefinitionKeys::default(),
                vec![],
                vec![],
                None,
            );
        }
        for i in 0..5 {
            let _ = self.get_symbol_with_attributes(
                wrap_symbol!(format!("symbolica::fl{}", i)),
                &[SymbolAttribute::Linear],
                None,
                None,
                None,
                None,
                None,
                CustomFunctionDefinitionKeys::default(),
                vec![],
                vec![],
                None,
            );
        }
        for i in 0..5 {
            let _ = self.get_symbol_with_attributes(
                wrap_symbol!(format!("symbolica::fsl{}", i)),
                &[SymbolAttribute::Symmetric, SymbolAttribute::Linear],
                None,
                None,
                None,
                None,
                None,
                CustomFunctionDefinitionKeys::default(),
                vec![],
                vec![],
                None,
            );
        }
    }

    /// Remove all user-defined symbols from the state. This will invalidate all
    /// currently existing atoms, and hence this function is unsafe.
    ///
    /// Example:
    /// ```
    /// # use symbolica::prelude::*;
    /// symbol!("f"; Symmetric);
    /// unsafe { State::reset(); }
    /// symbol!("f"; Antisymmetric);
    /// ```
    pub unsafe fn reset() {
        let mut state = Self::get_global_state().write().unwrap();

        state.str_to_id.clear();
        SYMBOL_OFFSET.store(ID_TO_STR.len(), Ordering::Relaxed);

        state.initialize_builtin_symbols();

        #[cfg(test)]
        {
            state.initialize_test();
        }
    }

    #[inline(always)]
    #[allow(dead_code)]
    pub(crate) unsafe fn symbol_from_id(id: u32) -> Symbol {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        ID_TO_STR[id as usize].0
    }

    /// Iterate over all defined symbols.
    pub fn symbol_iter() -> impl Iterator<Item = (Symbol, &'static str)> {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        ID_TO_STR
            .iter()
            .skip(SYMBOL_OFFSET.load(Ordering::Relaxed))
            .map(|s| (s.0, s.1.name.as_str()))
    }

    /// Returns `true` iff this identifier is defined by Symbolica.
    pub(crate) fn is_fixed_builtin(id: Symbol) -> bool {
        id.get_id() < Self::BUILTIN_SYMBOL_NAMES.len() as u32
    }

    /// Get the symbol for a certain name if the name is already registered,
    pub(crate) fn fetch_symbol(&self, name: &str) -> Option<Symbol> {
        self.str_to_id.get(name).cloned()
    }

    /// Get the next symbol index that will be assigned.
    pub(crate) fn get_next_symbol_index(&self) -> u32 {
        let offset = SYMBOL_OFFSET.load(Ordering::Relaxed);
        (ID_TO_STR.len() - offset) as u32
    }

    /// Get the wildcard level of a symbol name.
    pub(crate) fn get_wildcard_level(str: &str) -> u8 {
        let mut wildcard_level = 0;
        for x in str.chars().rev() {
            if x != '_' {
                break;
            }
            wildcard_level += 1;
        }
        wildcard_level
    }

    /// Get the symbol for a certain name if the name is already registered,
    /// else register it and return a new symbol without attributes.
    pub(crate) fn get_symbol(&mut self, name: NamespacedSymbol) -> Result<Symbol, String> {
        match self.str_to_id.entry(name.symbol.into()) {
            Entry::Occupied(o) => Ok(*o.get()),
            Entry::Vacant(v) => {
                let offset = SYMBOL_OFFSET.load(Ordering::Relaxed);
                if ID_TO_STR.len() - offset == u32::MAX as usize - 1 {
                    panic!("Too many variables defined");
                }

                let wildcard_level = State::get_wildcard_level(v.key());

                // there is no synchronization issue since only one thread can insert at a time
                // as the state itself is behind a mutex
                let id = ID_TO_STR.len() - offset;
                let new_symbol = Symbol::raw_var(id as u32, wildcard_level);
                let id_ret = ID_TO_STR.push((
                    new_symbol,
                    SymbolData {
                        name: v.key().clone(),
                        file: name.file,
                        namespace: name.namespace,
                        line: name.line,
                        aliases: vec![],
                        custom_normalization: None,
                        custom_print: None,
                        custom_derivative: None,
                        custom_series: None,
                        custom_evaluation: None,
                        custom_function_keys: CustomFunctionDefinitionKeys::default(),
                        tags: vec![],
                        user_data: UserData::None,
                    },
                )) - offset;
                assert_eq!(id, id_ret);

                v.insert(new_symbol);
                Ok(new_symbol)
            }
        }
    }

    pub(crate) fn get_state_mut() -> RwLockWriteGuard<'static, State> {
        Self::initialize_state();
        STATE.get().unwrap().write().unwrap()
    }

    /// Register a new symbol with the given attributes and a specific function
    /// that is called after normalization of the arguments. This function cannot
    /// be exported, and therefore before importing a state, symbols with special
    /// normalization functions must be registered explicitly.
    ///
    /// If the symbol already exists, an error is returned.
    pub(crate) fn get_symbol_with_attributes(
        &mut self,
        name: NamespacedSymbol,
        attributes: &[SymbolAttribute],
        normalization_function: Option<NormalizationFunction>,
        print_function: Option<PrintFunction>,
        derivative_function: Option<DerivativeFunction>,
        series_function: Option<Box<SeriesExpansionFunction>>,
        evaluation_function: Option<EvaluationInfo>,
        custom_function_keys: CustomFunctionDefinitionKeys,
        tags: Vec<std::string::String>,
        mut aliases: Vec<std::string::String>,
        user_data: Option<UserData>,
    ) -> Result<Symbol, String> {
        for alias in &mut aliases {
            if !alias.contains("::") {
                *alias = format!("{}::{}", name.namespace, alias);
            } else if !alias.starts_with(name.namespace.as_ref()) {
                return Err(format!(
                    "Alias {alias} defined in different namespace from main symbol namespace {}",
                    name.namespace
                )
                .into());
            }
        }

        match self.str_to_id.entry(name.symbol.into()) {
            Entry::Occupied(o) => {
                let r = *o.get();
                let data = &ID_TO_STR[r.get_id() as usize].1;

                let new_id = Symbol::raw_fn(
                    r.get_id(),
                    r.get_wildcard_level(),
                    attributes.contains(&SymbolAttribute::Symmetric),
                    attributes.contains(&SymbolAttribute::Antisymmetric),
                    attributes.contains(&SymbolAttribute::Cyclesymmetric),
                    attributes.contains(&SymbolAttribute::Linear),
                    attributes.contains(&SymbolAttribute::Flat),
                    attributes.contains(&SymbolAttribute::Scalar),
                    attributes.contains(&SymbolAttribute::Real),
                    attributes.contains(&SymbolAttribute::Integer),
                    attributes.contains(&SymbolAttribute::Positive),
                );

                if r.get_wildcard_level() == new_id.get_wildcard_level()
                    && r.is_symmetric() == new_id.is_symmetric()
                    && r.is_antisymmetric() == new_id.is_antisymmetric()
                    && r.is_cyclesymmetric() == new_id.is_cyclesymmetric()
                    && r.is_linear() == new_id.is_linear()
                    && r.is_flat() == new_id.is_flat()
                    && r.is_scalar() == new_id.is_scalar()
                    && r.is_real() == new_id.is_real()
                    && r.is_integer() == new_id.is_integer()
                    && r.is_positive() == new_id.is_positive()
                    && custom_function_matches(
                        &normalization_function,
                        &custom_function_keys.normalization,
                        &data.custom_normalization,
                        &data.custom_function_keys.normalization,
                    )
                    && custom_function_matches(
                        &print_function,
                        &custom_function_keys.print,
                        &data.custom_print,
                        &data.custom_function_keys.print,
                    )
                    && custom_function_matches(
                        &derivative_function,
                        &custom_function_keys.derivative,
                        &data.custom_derivative,
                        &data.custom_function_keys.derivative,
                    )
                    && custom_function_matches(
                        &series_function,
                        &custom_function_keys.series,
                        &data.custom_series,
                        &data.custom_function_keys.series,
                    )
                    && custom_function_matches(
                        &evaluation_function,
                        &custom_function_keys.evaluation,
                        &data.custom_evaluation,
                        &data.custom_function_keys.evaluation,
                    )
                    && tags == r.get_tags()
                    && aliases == r.get_aliases()
                    && user_data.as_ref().unwrap_or(&UserData::None)
                        == &ID_TO_STR[r.get_id() as usize].1.user_data
                {
                    Ok(r)
                } else {
                    let mut diff_attr = String::new();
                    if r.is_antisymmetric() != new_id.is_antisymmetric() {
                        diff_attr.push_str(&format!(
                            "\t- antisymmetric: {} vs {}\n",
                            r.is_antisymmetric(),
                            new_id.is_antisymmetric()
                        ));
                    }
                    if r.is_symmetric() != new_id.is_symmetric() {
                        diff_attr.push_str(&format!(
                            "\t- symmetric: {} vs {}\n",
                            r.is_symmetric(),
                            new_id.is_symmetric()
                        ));
                    }
                    if r.is_cyclesymmetric() != new_id.is_cyclesymmetric() {
                        diff_attr.push_str(&format!(
                            "\t- cyclesymmetric: {} vs {}\n",
                            r.is_cyclesymmetric(),
                            new_id.is_cyclesymmetric()
                        ));
                    }
                    if r.is_linear() != new_id.is_linear() {
                        diff_attr.push_str(&format!(
                            "\t- linear: {} vs {}\n",
                            r.is_linear(),
                            new_id.is_linear()
                        ));
                    }
                    if r.is_flat() != new_id.is_flat() {
                        diff_attr.push_str(&format!(
                            "\t- flat: {} vs {}\n",
                            r.is_flat(),
                            new_id.is_flat()
                        ));
                    }
                    if r.is_scalar() != new_id.is_scalar() {
                        diff_attr.push_str(&format!(
                            "\t- scalar: {} vs {}\n",
                            r.is_scalar(),
                            new_id.is_scalar()
                        ));
                    }
                    if r.is_real() != new_id.is_real() {
                        diff_attr.push_str(&format!(
                            "\t- real: {} vs {}\n",
                            r.is_real(),
                            new_id.is_real()
                        ));
                    }
                    if r.is_integer() != new_id.is_integer() {
                        diff_attr.push_str(&format!(
                            "\t- integer: {} vs {}\n",
                            r.is_integer(),
                            new_id.is_integer()
                        ));
                    }
                    if r.is_positive() != new_id.is_positive() {
                        diff_attr.push_str(&format!(
                            "\t- positive: {} vs {}\n",
                            r.is_positive(),
                            new_id.is_positive()
                        ));
                    }

                    if tags != r.get_tags() {
                        diff_attr.push_str(&format!(
                            "\t- tags: {:?} vs {:?}\n",
                            r.get_tags(),
                            tags
                        ));
                    }

                    if aliases != r.get_aliases() {
                        diff_attr.push_str(&format!(
                            "\t- aliases: {:?} vs {:?}\n",
                            r.get_aliases(),
                            aliases
                        ));
                    }

                    if !custom_function_matches(
                        &normalization_function,
                        &custom_function_keys.normalization,
                        &data.custom_normalization,
                        &data.custom_function_keys.normalization,
                    ) {
                        diff_attr.push_str("\t- new normalization function specified.\n");
                    }
                    if !custom_function_matches(
                        &print_function,
                        &custom_function_keys.print,
                        &data.custom_print,
                        &data.custom_function_keys.print,
                    ) {
                        diff_attr.push_str("\t- new print function specified.\n");
                    }
                    if !custom_function_matches(
                        &derivative_function,
                        &custom_function_keys.derivative,
                        &data.custom_derivative,
                        &data.custom_function_keys.derivative,
                    ) {
                        diff_attr.push_str("\t- new derivative function specified.\n");
                    }
                    if !custom_function_matches(
                        &series_function,
                        &custom_function_keys.series,
                        &data.custom_series,
                        &data.custom_function_keys.series,
                    ) {
                        diff_attr.push_str("\t- new series function specified.\n");
                    }
                    if !custom_function_matches(
                        &evaluation_function,
                        &custom_function_keys.evaluation,
                        &data.custom_evaluation,
                        &data.custom_function_keys.evaluation,
                    ) {
                        diff_attr.push_str("\t- new evaluation function specified.\n");
                    }

                    if user_data.as_ref().unwrap_or(&UserData::None) != &data.user_data {
                        diff_attr.push_str(&format!(
                            "\t- new user data specified: {:?} vs {:?}\n",
                            data.user_data, user_data
                        ));
                    }

                    if data.file.is_empty() {
                        Err(format!(
                            "Symbol {} redefined with new attributes:\n{}",
                            data.name, diff_attr
                        )
                        .into())
                    } else {
                        Err(format!("Symbol {} redefined with new attributes:\n{}\nThe first definition occurred here: {}:{}.", data.name, diff_attr, data.file, data.line).into())
                    }
                }
            }
            Entry::Vacant(v) => {
                let offset = SYMBOL_OFFSET.load(Ordering::Relaxed);
                if ID_TO_STR.len() - offset == u32::MAX as usize - 1 {
                    panic!("Too many variables defined");
                }

                // there is no synchronization issue since only one thread can insert at a time
                // as the state itself is behind a mutex
                let id = ID_TO_STR.len() - offset;

                let wildcard_level = State::get_wildcard_level(v.key());

                let new_symbol = Symbol::raw_fn(
                    id as u32,
                    wildcard_level,
                    attributes.contains(&SymbolAttribute::Symmetric),
                    attributes.contains(&SymbolAttribute::Antisymmetric),
                    attributes.contains(&SymbolAttribute::Cyclesymmetric),
                    attributes.contains(&SymbolAttribute::Linear),
                    attributes.contains(&SymbolAttribute::Flat),
                    attributes.contains(&SymbolAttribute::Scalar),
                    attributes.contains(&SymbolAttribute::Real),
                    attributes.contains(&SymbolAttribute::Integer),
                    attributes.contains(&SymbolAttribute::Positive),
                );

                let id_ret = ID_TO_STR.push((
                    new_symbol,
                    SymbolData {
                        name: v.key().clone(),
                        file: name.file,
                        namespace: name.namespace.clone(),
                        line: name.line,
                        custom_normalization: normalization_function,
                        custom_print: print_function,
                        custom_derivative: derivative_function,
                        custom_series: series_function,
                        custom_evaluation: evaluation_function,
                        custom_function_keys,
                        tags,
                        aliases: aliases.clone(),
                        user_data: user_data.unwrap_or(UserData::None),
                    },
                )) - offset;
                assert_eq!(id, id_ret);

                v.insert(new_symbol);

                if new_symbol.get_namespace() == "symbolica" {
                    self.builtin_symbols
                        .insert(new_symbol.get_stripped_name().into());
                }

                for alias in aliases {
                    match self.str_to_id.entry(alias.into()) {
                        Entry::Occupied(o) => {
                            let old_symbol = o.get();
                            let old_data = old_symbol.get_global_data();
                            if old_data.file.is_empty() {
                                return Err(
                                    format!("Alias {} already defined before", o.key()).into()
                                );
                            } else {
                                return Err(format!(
                                    "Alias {} already defined  here: {}:{}.",
                                    old_data.name, old_data.file, old_data.line
                                )
                                .into());
                            }
                        }
                        Entry::Vacant(v) => {
                            if new_symbol.get_namespace() == "symbolica" {
                                self.builtin_symbols.insert(v.key()[11..].into());
                            }

                            v.insert(new_symbol);
                        }
                    }
                }

                Ok(new_symbol)
            }
        }
    }

    /// Get the name for a given symbol.
    #[inline]
    pub(crate) fn get_name(id: Symbol) -> &'static str {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        &ID_TO_STR[id.get_id() as usize + SYMBOL_OFFSET.load(Ordering::Relaxed)]
            .1
            .name
    }

    /// Get the name for a given symbol.
    #[inline]
    pub(crate) fn get_symbol_namespace(id: Symbol) -> &'static str {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        ID_TO_STR[id.get_id() as usize + SYMBOL_OFFSET.load(Ordering::Relaxed)]
            .1
            .namespace
            .as_ref()
    }

    /// Get the name for a given symbol.
    #[inline]
    pub(crate) fn get_symbol_data(id: Symbol) -> &'static SymbolData {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        &ID_TO_STR[id.get_id() as usize + SYMBOL_OFFSET.load(Ordering::Relaxed)].1
    }

    /// Get the user-specified normalization function for the symbol.
    #[inline]
    pub(crate) fn get_normalization_function(id: Symbol) -> Option<&'static NormalizationFunction> {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        ID_TO_STR[id.get_id() as usize + SYMBOL_OFFSET.load(Ordering::Relaxed)]
            .1
            .custom_normalization
            .as_ref()
    }

    pub(crate) fn get_finite_field(fi: FiniteFieldIndex) -> &'static Zp64 {
        &FINITE_FIELDS[fi.0]
    }

    pub(crate) fn get_or_insert_finite_field(f: Zp64) -> FiniteFieldIndex {
        Self::get_global_state()
            .write()
            .unwrap()
            .get_or_insert_finite_field_impl(f)
    }

    pub(crate) fn get_or_insert_finite_field_impl(&mut self, f: Zp64) -> FiniteFieldIndex {
        for (i, f2) in FINITE_FIELDS.iter().enumerate() {
            if f.get_prime() == f2.get_prime() {
                return FiniteFieldIndex(i);
            }
        }

        let index = FINITE_FIELDS.push(f);
        FiniteFieldIndex(index)
    }

    pub(crate) fn get_variable_list(fi: VariableListIndex) -> Arc<Vec<PolyVariable>> {
        VARIABLE_LISTS[fi.0].clone()
    }

    pub(crate) fn get_or_insert_variable_list(f: Arc<Vec<PolyVariable>>) -> VariableListIndex {
        Self::get_global_state()
            .write()
            .unwrap()
            .get_or_insert_variable_list_impl(f)
    }

    pub(crate) fn get_or_insert_variable_list_impl(
        &mut self,
        f: Arc<Vec<PolyVariable>>,
    ) -> VariableListIndex {
        for (i, f2) in VARIABLE_LISTS.iter().enumerate() {
            if f2 == &f {
                return VariableListIndex(i);
            }
        }

        let index = VARIABLE_LISTS.push(f);
        VariableListIndex(index)
    }

    /// Write the state to a binary stream.
    #[inline(always)]
    pub fn export<W: Write>(dest: &mut W) -> Result<(), std::io::Error> {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        let all_symbols: HashSet<_> = State::symbol_iter().map(|(symbol, _)| symbol).collect();
        collect_export_symbols(&all_symbols, &HashSet::default())?;

        dest.write_u32::<LittleEndian>(SYMBOLICA_MAGIC)?;
        dest.write_u16::<LittleEndian>(EXPORT_FORMAT_VERSION)?;
        dest.write_u8(FULL_STATE_EXPORT_FLAG)?;

        dest.write_u64::<LittleEndian>(
            ID_TO_STR.len() as u64 - SYMBOL_OFFSET.load(Ordering::Relaxed) as u64,
        )?;

        for (s, _) in State::symbol_iter() {
            s.export(dest)?;
        }

        dest.write_u64::<LittleEndian>(FINITE_FIELDS.len() as u64)?;
        for x in FINITE_FIELDS.iter() {
            dest.write_u64::<LittleEndian>(x.get_prime())?;
        }

        dest.write_u64::<LittleEndian>(VARIABLE_LISTS.len() as u64)?;
        for x in VARIABLE_LISTS.iter() {
            dest.write_u64::<LittleEndian>(x.len() as u64)?;
            for y in x.iter() {
                match y {
                    PolyVariable::Symbol(s) => {
                        dest.write_u8(0)?;
                        dest.write_u32::<LittleEndian>(s.get_id())?;
                    }
                    PolyVariable::Temporary(u) => {
                        dest.write_u8(1)?;
                        dest.write_u64::<LittleEndian>(*u as u64)?;
                    }
                    PolyVariable::Function(v, t) => {
                        dest.write_u8(2)?;
                        dest.write_u32::<LittleEndian>(v.get_id())?;
                        t.as_view().write(dest.by_ref())?;
                    }
                    PolyVariable::Power(t) => {
                        dest.write_u8(3)?;
                        t.as_view().write(dest.by_ref())?;
                    }
                }
            }
        }

        Ok(())
    }

    /// Write the state of a part of the symbol table to a binary stream.
    #[inline(always)]
    pub fn export_partial<W: Write>(
        dest: &mut W,
        symbols: HashSet<Symbol>,
    ) -> Result<(), std::io::Error> {
        Self::export_partial_with_variable_lists(dest, &symbols, &HashSet::default())
    }

    pub(crate) fn export_partial_atom<W: Write>(
        dest: &mut W,
        atom: AtomView<'_>,
    ) -> Result<(), std::io::Error> {
        let mut dependencies = StateDependencies::default();
        dependencies.add_atom(atom);
        let symbols = atom.get_all_symbols(true);
        Self::export_partial_with_variable_lists(dest, &symbols, &dependencies.variable_lists)
    }

    fn export_partial_with_variable_lists<W: Write>(
        dest: &mut W,
        symbols: &HashSet<Symbol>,
        variable_lists: &HashSet<u64>,
    ) -> Result<(), std::io::Error> {
        if ID_TO_STR.len() == 0 {
            Self::initialize_state();
        }

        let symbols = collect_export_symbols(symbols, variable_lists)?;
        dest.write_u32::<LittleEndian>(SYMBOLICA_MAGIC)?;
        dest.write_u16::<LittleEndian>(EXPORT_FORMAT_VERSION)?;
        dest.write_u8(!FULL_STATE_EXPORT_FLAG)?;

        dest.write_u64::<LittleEndian>(symbols.len() as u64)?;

        for (i, (s, _)) in State::symbol_iter().enumerate() {
            if symbols.contains(&s) {
                dest.write_u32::<LittleEndian>(i as u32)?;
                s.export(dest)?;
            }
        }

        dest.write_u64::<LittleEndian>(FINITE_FIELDS.len() as u64)?;
        for x in FINITE_FIELDS.iter() {
            dest.write_u64::<LittleEndian>(x.get_prime())?;
        }

        dest.write_u64::<LittleEndian>(VARIABLE_LISTS.len() as u64)?;
        for x in VARIABLE_LISTS.iter() {
            dest.write_u64::<LittleEndian>(x.len() as u64)?;
            for y in x.iter() {
                match y {
                    PolyVariable::Symbol(s) => {
                        dest.write_u8(0)?;
                        dest.write_u32::<LittleEndian>(s.get_id())?;
                    }
                    PolyVariable::Temporary(u) => {
                        dest.write_u8(1)?;
                        dest.write_u64::<LittleEndian>(*u as u64)?;
                    }
                    PolyVariable::Function(v, t) => {
                        dest.write_u8(2)?;
                        dest.write_u32::<LittleEndian>(v.get_id())?;
                        t.as_view().write(dest.by_ref())?;
                    }
                    PolyVariable::Power(t) => {
                        dest.write_u8(3)?;
                        t.as_view().write(dest.by_ref())?;
                    }
                }
            }
        }

        Ok(())
    }

    /// Import a state, merging it with the current state.
    /// Upon a conflict, i.e. when a symbol with the same name but different attributes is
    /// encountered, `conflict_fn` is called with the conflicting name as argument which
    /// should yield a new name for the symbol.
    #[inline(always)]
    pub fn import<R: Read>(
        source: &mut R,
        conflict_fn: Option<Box<dyn Fn(&str) -> String>>,
    ) -> Result<StateMap, std::io::Error> {
        let magic = source.read_u32::<LittleEndian>()?;

        if magic != SYMBOLICA_MAGIC {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Invalid magic number: the file is not exported from Symbolica",
            ));
        }

        let version = source.read_u16::<LittleEndian>()?;
        if !SUPPORTED_IMPORT_VERSIONS.contains(&version) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!(
                    "Invalid export format version: expected {} but got {}",
                    EXPORT_FORMAT_VERSION, version
                ),
            ));
        }

        let is_full_state = if version > 4 {
            source.read_u8()? == FULL_STATE_EXPORT_FLAG
        } else {
            true
        };

        let n_symbols = source.read_u64::<LittleEndian>()?;
        let mut imported_symbols = Vec::with_capacity(n_symbols as usize);
        for mut index in 0..n_symbols {
            if !is_full_state {
                index = source.read_u32::<LittleEndian>()? as u64
            }
            if index > u32::MAX as u64 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("Symbol index {index} does not fit in the v5 symbol id space"),
                ));
            }

            let (name, namespace, attributes, tags, user_data, aliases, is_exportable) =
                Symbol::import_impl(source)?;
            imported_symbols.push(Some(ImportedSymbol {
                index: index as u32,
                name,
                namespace,
                attributes,
                tags,
                user_data,
                aliases,
                is_exportable,
            }));
        }

        let mut state_map = StateMap::default();
        let n_finite_fields = source.read_u64::<LittleEndian>()?;
        for x in 0..n_finite_fields {
            let prime = source.read_u64::<LittleEndian>()?;
            let id = State::get_or_insert_finite_field(Zp64::new(prime));
            if x != id.0 as u64 {
                state_map
                    .finite_fields
                    .insert(FiniteFieldIndex(x as usize), id);
            }
        }

        let n_variable_lists = source.read_u64::<LittleEndian>()?;
        let mut imported_variable_lists = Vec::with_capacity(n_variable_lists as usize);
        for x in 0..n_variable_lists {
            let n_vars = source.read_u64::<LittleEndian>()?;
            let mut variables = Vec::with_capacity(n_vars as usize);
            for _ in 0..n_vars {
                match source.read_u8()? {
                    0 => {
                        let id = source.read_u32::<LittleEndian>()?;
                        variables.push(ImportedPolyVariable::Symbol(id));
                    }
                    1 => {
                        let u = source.read_u64::<LittleEndian>()?;
                        variables.push(ImportedPolyVariable::Temporary(u as usize));
                    }
                    2 => {
                        let id = source.read_u32::<LittleEndian>()?;
                        let mut f = Atom::new();
                        f.read(&mut *source)?;
                        variables.push(ImportedPolyVariable::Function(id, f));
                    }
                    3 => {
                        let mut f = Atom::new();
                        f.read(&mut *source)?;
                        variables.push(ImportedPolyVariable::Power(f));
                    }
                    _ => {
                        return Err(std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            "Invalid variable type",
                        ));
                    }
                }
            }
            imported_variable_lists.push(Some(ImportedVariableList {
                index: x,
                variables,
            }));
        }

        let imported_symbol_ids: HashSet<_> = imported_symbols
            .iter()
            .flatten()
            .map(|record| record.index)
            .collect();
        if imported_symbol_ids.len() != imported_symbols.len() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "State contains duplicate symbol indices",
            ));
        }
        for record in imported_symbols.iter().flatten() {
            let mut dependencies = StateDependencies::default();
            dependencies.add_user_data(&record.user_data);
            if let Some(id) = dependencies
                .symbols
                .iter()
                .find(|id| !imported_symbol_ids.contains(id))
            {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "User data for symbol {} references non-exported symbol id {id}",
                        record.name
                    ),
                ));
            }
            if let Some(index) = dependencies
                .variable_lists
                .iter()
                .find(|index| **index >= n_variable_lists)
            {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "User data for symbol {} references missing variable list {index}",
                        record.name
                    ),
                ));
            }
        }
        // A v5 partial state still contains the process's complete variable-list
        // table. Lists unrelated to the exported expression may consequently
        // reference symbols omitted from the partial symbol table. Ignore those
        // unreachable lists, while retaining every closed list for dependency
        // resolution and cycle detection.
        let mut available_variable_lists: HashSet<_> = (0..n_variable_lists).collect();
        loop {
            let previous_len = available_variable_lists.len();
            for record in imported_variable_lists.iter().flatten() {
                if !available_variable_lists.contains(&record.index) {
                    continue;
                }
                let mut dependencies = StateDependencies::default();
                for variable in &record.variables {
                    dependencies.add_imported_variable(variable);
                }
                if !dependencies
                    .symbols
                    .iter()
                    .all(|id| imported_symbol_ids.contains(id))
                    || !dependencies
                        .variable_lists
                        .iter()
                        .all(|index| available_variable_lists.contains(index))
                {
                    available_variable_lists.remove(&record.index);
                }
            }
            if available_variable_lists.len() == previous_len {
                break;
            }
        }
        for pending in &mut imported_variable_lists {
            if pending
                .as_ref()
                .is_some_and(|record| !available_variable_lists.contains(&record.index))
            {
                *pending = None;
            }
        }

        let mut resolved_symbols = HashMap::default();
        let mut resolved_variable_lists = HashMap::default();
        let mut remaining = imported_symbols.iter().flatten().count()
            + imported_variable_lists.iter().flatten().count();
        while remaining != 0 {
            let mut progress = false;

            for pending in &mut imported_symbols {
                let Some(record) = pending.as_ref() else {
                    continue;
                };
                let mut dependencies = StateDependencies::default();
                dependencies.add_user_data(&record.user_data);
                if !dependencies
                    .symbols
                    .iter()
                    .all(|id| resolved_symbols.contains_key(id))
                    || !dependencies
                        .variable_lists
                        .iter()
                        .all(|index| resolved_variable_lists.contains_key(index))
                {
                    continue;
                }

                let record = pending.take().unwrap();
                let old_index = record.index;
                let symbol = register_imported_symbol(record, &state_map, conflict_fn.as_deref())?;
                resolved_symbols.insert(old_index, symbol);
                if old_index != symbol.get_id() {
                    state_map.symbols.insert(old_index, symbol);
                }
                remaining -= 1;
                progress = true;
            }

            for pending in &mut imported_variable_lists {
                let Some(record) = pending.as_ref() else {
                    continue;
                };
                let mut dependencies = StateDependencies::default();
                for variable in &record.variables {
                    dependencies.add_imported_variable(variable);
                }
                if !dependencies
                    .symbols
                    .iter()
                    .all(|id| resolved_symbols.contains_key(id))
                    || !dependencies
                        .variable_lists
                        .iter()
                        .all(|index| resolved_variable_lists.contains_key(index))
                {
                    continue;
                }

                let record = pending.take().unwrap();
                let old_index = record.index;
                let variables = resolve_variable_list(record, &resolved_symbols, &state_map)?;
                let new_index = State::get_or_insert_variable_list(variables.clone());
                resolved_variable_lists.insert(old_index, variables.clone());
                if old_index != new_index.0 as u64 {
                    state_map.variables_lists.insert(old_index, variables);
                }
                remaining -= 1;
                progress = true;
            }

            if !progress {
                let pending_symbols: Vec<_> = imported_symbols
                    .iter()
                    .flatten()
                    .map(|record| record.name.as_str())
                    .collect();
                let pending_variable_lists: Vec<_> = imported_variable_lists
                    .iter()
                    .flatten()
                    .map(|record| record.index)
                    .collect();
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "Cyclic state dependencies while importing symbols {pending_symbols:?} and variable lists {pending_variable_lists:?}"
                    ),
                ));
            }
        }

        Ok(state_map)
    }
}

/// A workspace that stores recyclable atoms. Upon dropping, the atoms automatically returned to a
/// thread-local workspace (which may be a different one than the one it was created by).
pub struct Workspace {
    atom_buffer: RefCell<Vec<Atom>>,
}

impl Workspace {
    const ATOM_BUFFER_MAX: usize = 30;
    const ATOM_CACHE_SIZE_MAX: usize = 20_000_000;

    /// Create a new workspace.
    const fn new() -> Self {
        Workspace {
            atom_buffer: RefCell::new(Vec::new()),
        }
    }

    /// Get a thread-local workspace.
    #[inline]
    pub fn get_local() -> &'static LocalKey<Workspace> {
        LicenseManager::check();

        &WORKSPACE
    }

    /// Return a recycled atom from this workspace. The atom may have the same value as before.
    #[inline]
    pub fn new_atom(&self) -> RecycledAtom {
        if let Ok(mut a) = self.atom_buffer.try_borrow_mut() {
            if let Some(b) = a.pop() {
                b.into()
            } else {
                Atom::default().into()
            }
        } else {
            Atom::default().into() // very rare
        }
    }

    /// Create a new variable from a recycled atom from this workspace.
    #[inline]
    pub fn new_var(&self, id: Symbol) -> RecycledAtom {
        let mut owned = self.new_atom();
        owned.to_var(id);
        owned
    }

    /// Create a new number from a recycled atom from this workspace.
    #[inline]
    pub fn new_num<T: Into<Coefficient>>(&self, num: T) -> RecycledAtom {
        let mut owned = self.new_atom();
        owned.to_num(num);
        owned
    }

    pub fn return_atom(&self, atom: Atom) {
        if let Ok(mut a) = self.atom_buffer.try_borrow_mut() {
            a.push(atom);
        }
    }
}

/// A wrapper around [Atom] that stores the underlying buffer
/// in a thread-local storage cache when dropped.
#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub struct RecycledAtom(Atom);

impl From<Atom> for RecycledAtom {
    fn from(a: Atom) -> Self {
        RecycledAtom(a)
    }
}

impl std::fmt::Display for RecycledAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Default for RecycledAtom {
    fn default() -> Self {
        Self::new()
    }
}

impl RecycledAtom {
    /// Get a recycled atom from a thread-local workspace.
    #[inline]
    pub fn new() -> RecycledAtom {
        Workspace::get_local().with(|ws| ws.new_atom())
    }

    /// Wrap an atom so that it gets recycled upon dropping.
    pub fn wrap(atom: Atom) -> RecycledAtom {
        RecycledAtom(atom)
    }

    #[inline]
    pub fn new_var(id: Symbol) -> RecycledAtom {
        let mut owned = Self::new();
        owned.to_var(id);
        owned
    }

    /// Create a new number from a recycled atom from this workspace.
    #[inline]
    pub fn new_num<T: Into<Coefficient>>(num: T) -> RecycledAtom {
        let mut owned = Self::new();
        owned.to_num(num);
        owned
    }

    /// Yield the atom, which will now no longer be recycled upon dropping.
    pub fn into_inner(mut self) -> Atom {
        std::mem::replace(&mut self.0, Atom::Zero)
    }
}

impl Deref for RecycledAtom {
    type Target = Atom;

    fn deref(&self) -> &Atom {
        &self.0
    }
}

impl DerefMut for RecycledAtom {
    fn deref_mut(&mut self) -> &mut Atom {
        &mut self.0
    }
}

impl AsRef<Atom> for RecycledAtom {
    fn as_ref(&self) -> &Atom {
        self.deref()
    }
}

impl Drop for RecycledAtom {
    #[inline]
    fn drop(&mut self) {
        if let Atom::Zero = self.0 {
            return;
        }

        if self.0.get_capacity() > Workspace::ATOM_CACHE_SIZE_MAX {
            return;
        }

        let _ = WORKSPACE.try_with(
            #[inline(always)]
            |ws| {
                if let Ok(mut a) = ws.atom_buffer.try_borrow_mut()
                    && a.len() < Workspace::ATOM_BUFFER_MAX
                {
                    a.push(std::mem::replace(&mut self.0, Atom::Zero));
                }
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use byteorder::{LittleEndian, WriteBytesExt};

    use crate::{
        atom::{Atom, AtomCore, AtomView, InlineVar, NormalizationFunction, Symbol, UserData},
        parse,
        printer::PrintFunction,
        symbol, wrap_symbol,
    };

    use super::{CustomFunctionDefinitionKeys, EXPORT_FORMAT_VERSION, SYMBOLICA_MAGIC, State};

    fn test_print_function() -> PrintFunction {
        Box::new(|_, _, _| Some("test".into()))
    }

    fn test_normalization_function() -> NormalizationFunction {
        Box::new(|_, _| {})
    }

    fn write_v5_symbol(output: &mut Vec<u8>, index: u32, name: &str, user_data: &UserData) {
        output.write_u32::<LittleEndian>(index).unwrap();
        output.write_u32::<LittleEndian>(name.len() as u32).unwrap();
        output.extend_from_slice(name.as_bytes());
        let namespace = name.rsplit_once("::").unwrap().0;
        output
            .write_u32::<LittleEndian>(namespace.len() as u32)
            .unwrap();
        output.extend_from_slice(namespace.as_bytes());
        output.write_u8(0).unwrap(); // symbol flags
        output.write_u32::<LittleEndian>(0).unwrap(); // extra symbol flags
        output.write_u16::<LittleEndian>(0).unwrap(); // tags
        output.write_u16::<LittleEndian>(0).unwrap(); // aliases
        user_data.write(output).unwrap();
        output.write_u8(1).unwrap(); // exportable
    }

    fn v5_partial_state_header(symbol_count: u64) -> Vec<u8> {
        let mut output = vec![];
        output.write_u32::<LittleEndian>(SYMBOLICA_MAGIC).unwrap();
        output.write_u16::<LittleEndian>(5).unwrap();
        output.write_u8(0).unwrap(); // partial state
        output.write_u64::<LittleEndian>(symbol_count).unwrap();
        output
    }

    #[test]
    fn state_export_import() {
        let mut export = vec![];
        State::export(&mut export).unwrap();

        let i = State::import(&mut export.as_slice(), None).unwrap();
        assert!(i.is_empty());

        imports_pre_dependency_v5_fixture();
        rejects_unresolved_user_data_dependency();
        rejects_cyclic_user_data_dependencies();
    }

    fn imports_pre_dependency_v5_fixture() {
        assert_eq!(EXPORT_FORMAT_VERSION, 5);

        let old_id = 1_000_100;
        let name = "state_fixture::legacy_v5_symbol";
        let mut fixture = v5_partial_state_header(1);
        write_v5_symbol(&mut fixture, old_id, name, &UserData::None);
        fixture.write_u64::<LittleEndian>(0).unwrap(); // finite fields
        fixture.write_u64::<LittleEndian>(0).unwrap(); // variable lists
        fixture.write_u64::<LittleEndian>(1).unwrap(); // expressions
        Atom::var(Symbol::raw_var(old_id, 0))
            .as_view()
            .write(&mut fixture)
            .unwrap();

        let imported = Atom::import(&mut fixture.as_slice(), None).unwrap();
        assert_eq!(imported.get_symbol().unwrap().get_name(), name);
    }

    fn rejects_unresolved_user_data_dependency() {
        let old_id = 1_000_200;
        let missing_id = old_id + 1;
        let mut fixture = v5_partial_state_header(1);
        write_v5_symbol(
            &mut fixture,
            old_id,
            "state_fixture::unresolved_owner",
            &UserData::Atom(Atom::var(Symbol::raw_var(missing_id, 0))),
        );
        fixture.write_u64::<LittleEndian>(0).unwrap();
        fixture.write_u64::<LittleEndian>(0).unwrap();

        let error = match State::import(&mut fixture.as_slice(), None) {
            Ok(_) => panic!("unresolved dependency was accepted"),
            Err(error) => error,
        };
        assert!(error.to_string().contains("non-exported symbol id"));
    }

    fn rejects_cyclic_user_data_dependencies() {
        let first_id = 1_000_300;
        let second_id = first_id + 1;
        let mut fixture = v5_partial_state_header(2);
        write_v5_symbol(
            &mut fixture,
            first_id,
            "state_fixture::cycle_a",
            &UserData::Atom(Atom::var(Symbol::raw_var(second_id, 0))),
        );
        write_v5_symbol(
            &mut fixture,
            second_id,
            "state_fixture::cycle_b",
            &UserData::Atom(Atom::var(Symbol::raw_var(first_id, 0))),
        );
        fixture.write_u64::<LittleEndian>(0).unwrap();
        fixture.write_u64::<LittleEndian>(0).unwrap();

        let error = match State::import(&mut fixture.as_slice(), None) {
            Ok(_) => panic!("cyclic dependencies were accepted"),
            Err(error) => error,
        };
        assert!(error.to_string().contains("Cyclic state dependencies"));
    }

    #[test]
    fn export_symbol_data() {
        let s = symbol!(
            "symbolica::symbol_data::a",
            data = crate::state::UserData::Atom(parse!("z"))
        );

        let s1 = s.to_atom();
        let mut export = vec![];
        s1.export(&mut export).unwrap();

        let a = Atom::import(&mut export.as_slice(), None)
            .unwrap()
            .get_symbol()
            .unwrap();
        assert_eq!(a.get_data(), &crate::state::UserData::Atom(parse!("z")));
    }

    #[test]
    fn custom_function_definition_keys_are_opt_in() {
        let name = wrap_symbol!("symbolica::keyed_normalization_redefinition");
        let key = b"same Python transformer".to_vec();

        let first = State::get_state_mut()
            .get_symbol_with_attributes(
                name.clone(),
                &[],
                Some(test_normalization_function()),
                None,
                None,
                None,
                None,
                CustomFunctionDefinitionKeys {
                    normalization: Some(key.clone()),
                    ..Default::default()
                },
                vec![],
                vec![],
                None,
            )
            .unwrap();

        let repeated = State::get_state_mut()
            .get_symbol_with_attributes(
                name.clone(),
                &[],
                Some(test_normalization_function()),
                None,
                None,
                None,
                None,
                CustomFunctionDefinitionKeys {
                    normalization: Some(key),
                    ..Default::default()
                },
                vec![],
                vec![],
                None,
            )
            .unwrap();
        assert_eq!(first, repeated);

        let changed = State::get_state_mut().get_symbol_with_attributes(
            name,
            &[],
            Some(test_normalization_function()),
            None,
            None,
            None,
            None,
            CustomFunctionDefinitionKeys {
                normalization: Some(b"different Python transformer".to_vec()),
                ..Default::default()
            },
            vec![],
            vec![],
            None,
        );
        assert!(
            changed
                .unwrap_err()
                .contains("new normalization function specified")
        );

        let name = wrap_symbol!("symbolica::keyed_custom_function_redefinition");
        let key = b"same Python definition".to_vec();

        let first = State::get_state_mut()
            .get_symbol_with_attributes(
                name.clone(),
                &[],
                None,
                Some(test_print_function()),
                None,
                None,
                None,
                CustomFunctionDefinitionKeys {
                    print: Some(key.clone()),
                    ..Default::default()
                },
                vec![],
                vec![],
                None,
            )
            .unwrap();

        let repeated = State::get_state_mut()
            .get_symbol_with_attributes(
                name.clone(),
                &[],
                None,
                Some(test_print_function()),
                None,
                None,
                None,
                CustomFunctionDefinitionKeys {
                    print: Some(key),
                    ..Default::default()
                },
                vec![],
                vec![],
                None,
            )
            .unwrap();
        assert_eq!(first, repeated);

        let changed = State::get_state_mut().get_symbol_with_attributes(
            name,
            &[],
            None,
            Some(test_print_function()),
            None,
            None,
            None,
            CustomFunctionDefinitionKeys {
                print: Some(b"different Python definition".to_vec()),
                ..Default::default()
            },
            vec![],
            vec![],
            None,
        );
        assert!(
            changed
                .unwrap_err()
                .contains("new print function specified")
        );

        // Public Rust builders do not supply a definition key and therefore
        // retain the existing define-once behavior.
        let name = wrap_symbol!("symbolica::unkeyed_custom_function_redefinition");

        State::get_state_mut()
            .get_symbol_with_attributes(
                name.clone(),
                &[],
                None,
                Some(test_print_function()),
                None,
                None,
                None,
                CustomFunctionDefinitionKeys::default(),
                vec![],
                vec![],
                None,
            )
            .unwrap();

        let repeated = State::get_state_mut().get_symbol_with_attributes(
            name,
            &[],
            None,
            Some(test_print_function()),
            None,
            None,
            None,
            CustomFunctionDefinitionKeys::default(),
            vec![],
            vec![],
            None,
        );
        assert!(
            repeated
                .unwrap_err()
                .contains("new print function specified")
        );
    }

    #[test]
    fn custom_normalization() {
        let _real_log = symbol!(
            "custom_normalization_real_log",
            norm = |input, out| {
                if let AtomView::Fun(f) = input {
                    if f.get_nargs() == 1 {
                        let arg = f.iter().next().unwrap();
                        if let AtomView::Pow(p) = arg {
                            let (b, e) = p.get_base_exp();
                            if b == InlineVar::new(Symbol::E).as_view() {
                                out.set_from_view(&e);
                            }
                        }
                    }
                }
            }
        );

        let e = parse!("custom_normalization_real_log(exp(x))");
        assert_eq!(e, parse!("x"));
    }
}
