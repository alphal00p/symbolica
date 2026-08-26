use std::io::Cursor;

use smartstring::SmartString;
use symbolica::{
    atom::{Atom, AtomCore, UserData, UserDataKey},
    coefficient::Coefficient,
    domains::{integer::Z, rational::Q},
    parse,
    state::State,
    symbol,
};

fn conflict() {
    symbol!("x", "y");
    symbol!("f"; Symmetric);

    let a = parse!("f(x, y)*x^2");

    let mut a_export = vec![];
    a.as_view().write(&mut a_export).unwrap();

    let mut state_export = vec![];
    State::export(&mut state_export).unwrap();

    // reset the state and create a conflict
    unsafe { State::reset() };

    symbol!("y");
    symbol!("x");
    symbol!("f");

    let state_map = State::import(
        &mut Cursor::new(&state_export),
        Some(Box::new(|old_name| SmartString::from(old_name) + "1")),
    )
    .unwrap();

    let a_rec = Atom::import_with_map(&mut Cursor::new(&a_export), &state_map).unwrap();

    let r = parse!("x^2*f1(y, x)");
    assert_eq!(a_rec, r);
}

fn partial_state_export() {
    unsafe { State::reset() };

    // Interleave unused symbols so that the exported symbol IDs are sparse.
    symbol!("partial_export_unused_before");
    symbol!("partial_export_x");
    symbol!("partial_export_unused_between");
    symbol!("partial_export_f"; Symmetric);
    symbol!("partial_export_y");

    let a = parse!("partial_export_f(partial_export_y, partial_export_x)*partial_export_x^2");

    symbol!("partial_export_unused_after");

    let mut export = vec![];
    a.export(&mut export).unwrap();
    drop(a);

    unsafe { State::reset() };

    let a_rec = Atom::import(&mut export.as_slice(), None).unwrap();
    let expected =
        parse!("partial_export_f(partial_export_x, partial_export_y)*partial_export_x^2");
    assert_eq!(a_rec, expected);
    assert!(symbol!("partial_export_f").is_symmetric());

    let imported_names: Vec<_> = State::symbol_iter().map(|(_, name)| name).collect();
    assert!(
        !imported_names
            .iter()
            .any(|name| name.ends_with("partial_export_unused_before"))
    );
    assert!(
        !imported_names
            .iter()
            .any(|name| name.ends_with("partial_export_unused_between"))
    );
    assert!(
        !imported_names
            .iter()
            .any(|name| name.ends_with("partial_export_unused_after"))
    );
}

fn unchanged_function_head_remaps_arguments() {
    unsafe { State::reset() };

    symbol!("state_import::head_argument");
    symbol!("state_import::stable_head");
    let expression = parse!("state_import::stable_head(state_import::head_argument)");
    let mut export = vec![];
    expression.export(&mut export).unwrap();
    drop(expression);

    unsafe { State::reset() };
    symbol!("state_import::padding");
    symbol!("state_import::stable_head");

    let imported = Atom::import(&mut export.as_slice(), None).unwrap();
    assert_eq!(
        imported,
        parse!("state_import::stable_head(state_import::head_argument)")
    );
}

fn nested_user_data_round_trip() {
    unsafe { State::reset() };

    symbol!("state_import::data_leaf");
    let dependency = symbol!(
        "state_import::data_dependency",
        data = UserData::Atom(parse!("state_import::data_leaf"))
    );
    let key = UserDataKey::Atom(parse!("state_import::key_head(state_import::data_leaf)"));
    let value = UserData::List(vec![UserData::Atom(
        dependency.call(parse!("state_import::data_leaf")),
    )]);
    let owner = symbol!(
        "state_import::data_owner",
        data = UserData::Map([(key, value)].into_iter().collect())
    );
    let mut export = vec![];
    owner.to_atom().export(&mut export).unwrap();

    unsafe { State::reset() };
    symbol!(
        "state_import::data_padding_1",
        "state_import::data_padding_2"
    );

    let imported_owner = Atom::import(&mut export.as_slice(), None)
        .unwrap()
        .get_symbol()
        .unwrap();
    let UserData::Map(map) = imported_owner.get_data() else {
        panic!("expected imported map user data");
    };
    let expected_key = UserDataKey::Atom(parse!("state_import::key_head(state_import::data_leaf)"));
    let expected_value = UserData::List(vec![UserData::Atom(parse!(
        "state_import::data_dependency(state_import::data_leaf)"
    ))]);
    assert_eq!(map.get(&expected_key), Some(&expected_value));

    let imported_dependency = symbol!("state_import::data_dependency");
    assert_eq!(
        imported_dependency.get_data(),
        &UserData::Atom(parse!("state_import::data_leaf"))
    );
}

fn user_data_variable_list_dependency_order() {
    unsafe { State::reset() };

    symbol!("state_import::coefficient_parameter");
    let coefficient = parse!("1 + state_import::coefficient_parameter")
        .to_rational_polynomial::<_, _, u16>(&Q, &Z, None);
    let coefficient_atom = Atom::num(Coefficient::RationalPolynomial(coefficient));
    let owner = symbol!(
        "state_import::coefficient_owner",
        data = UserData::Atom(coefficient_atom)
    );
    let mut export = vec![];
    owner.to_atom().export(&mut export).unwrap();

    unsafe { State::reset() };
    let _padding = parse!("1 + state_import::coefficient_padding")
        .to_rational_polynomial::<_, _, u16>(&Q, &Z, None);

    let imported_owner = Atom::import(&mut export.as_slice(), None)
        .unwrap()
        .get_symbol()
        .unwrap();
    let expected = parse!("1 + state_import::coefficient_parameter")
        .to_rational_polynomial::<_, _, u16>(&Q, &Z, None);
    assert_eq!(
        imported_owner.get_data(),
        &UserData::Atom(Atom::num(Coefficient::RationalPolynomial(expected)))
    );
}

#[test]
fn rational_rename() {
    symbol!("x");

    let a = parse!("x^2*coeff(x)");

    let mut a_export = vec![];
    a.as_view().write(&mut a_export).unwrap();

    let mut state_export = vec![];
    State::export(&mut state_export).unwrap();

    // reset the state and create a conflict
    unsafe { State::reset() };

    symbol!("y");

    let state_map = State::import(&mut Cursor::new(&state_export), None).unwrap();

    let a_rec = Atom::import_with_map(&mut Cursor::new(&a_export), &state_map).unwrap();

    let r = parse!("x^2*coeff(x)");
    assert_eq!(a_rec, r);

    unsafe { State::reset() };
    conflict();
    partial_state_export();
    unchanged_function_head_remaps_arguments();
    nested_user_data_round_trip();
    user_data_variable_list_dependency_order();
}
