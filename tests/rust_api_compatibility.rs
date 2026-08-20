use std::sync::Arc;

use symbolica::{
    atom::{Atom, AtomCore},
    domains::{integer::Z, rational::Q},
    parse,
    poly::PolyVariable,
    symbol,
};

#[test]
fn legacy_rust_api_compatibility() {
    let system = [parse!("2*x+y-1"), parse!("x+y+1")];
    let variables = [parse!("x"), parse!("y")];

    let solution = Atom::solve_linear_system::<u8, _, _>(&system, &variables).unwrap();

    assert_eq!(solution, [Atom::num(2), Atom::num(-3)]);

    let mut rational = parse!("x/y").to_rational_polynomial::<_, _, u8>(&Q, &Z, None);
    let variables = Arc::new(vec![
        PolyVariable::Symbol(symbol!("u")),
        PolyVariable::Symbol(symbol!("v")),
    ]);

    // These assignments intentionally exercise the public field API used by
    // dependent crates written before polynomial contexts became shared.
    rational.numerator.variables = variables.clone();
    rational.denominator.variables = variables.clone();

    assert!(Arc::ptr_eq(rational.numerator.variables(), &variables));
    assert!(Arc::ptr_eq(rational.denominator.variables(), &variables));
}
