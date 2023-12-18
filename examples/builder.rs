use symbolica::{
    representations::{AsAtomView, Atom, FunctionBuilder,  },
    state::{FunctionAttribute, State, Workspace}, rings::{rational::Rational, },
};

// fn zeros<'a>(ws:&'a Workspace,state:&'a State) -> Vec<Expr<'a>>{

//     let zeroatom = ws.new_num(0).to_owned();
//     let zero = zeroatom.builder(&state, ws).to_owned();
//     vec![zero;3]
// } 

fn main() {
    let mut state = State::new();
    let ws: Workspace = Workspace::new();

    let x = Atom::parse("x", &mut state, &ws).unwrap();
    let y = Atom::parse("y", &mut state, &ws).unwrap();
    let f_id = state
        .get_or_insert_fn("f", Some(vec![FunctionAttribute::Symmetric]))
        .unwrap();
    let f = FunctionBuilder::new(f_id, &state, &ws)
        .add_arg(&ws.new_num(1))
        .finish();

    let fatom = Atom::new_from_view(&f.as_atom_view());

    // the cumbersome passing of the state and workspace can be avoided by using an
    // AtomBuilder, which accumulates the result
    let mut xb = x.builder(&state, &ws);

    // let rugrat=rug::Rational::from_f64(0.49).unwrap();
    // let natrat = Rational::from_large(rugrat);
    // ws.new_num(Number::from(natrat));

    // let syrn= symbolica::rings::rational::Rational::from_large(aruN);


    xb = (-(xb + &y + &x) * &y * &ws.new_num(6)).pow(&ws.new_num(5)) / &y * &fatom;

    println!("{}", xb.as_atom_view().printer(&state));
}
