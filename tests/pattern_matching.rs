use symbolica::{
    atom::{Atom, AtomCore, AtomView, Symbol},
    id::{Match, Pattern, WildcardRestriction},
    state::RecycledAtom,
};

#[test]
fn fibonacci() {
    // prepare all patterns
    let pattern = Pattern::parse("f(x_)").unwrap();
    let rhs = Pattern::parse("f(x_ - 1) + f(x_ - 2)").unwrap();
    let lhs_zero_pat = Pattern::parse("f(0)").unwrap();
    let lhs_one_pat = Pattern::parse("f(1)").unwrap();
    let rhs_one = Atom::new_num(1).to_pattern();

    // prepare the pattern restriction `x_ > 1`
    let restrictions = (
        Symbol::new("x_"),
        WildcardRestriction::Filter(Box::new(|v: &Match| match v {
            Match::Single(AtomView::Num(n)) => !n.is_one() && !n.is_zero(),
            _ => false,
        })),
    )
        .into();

    let input = Atom::parse("f(10)").unwrap();
    let mut target: RecycledAtom = input.clone().into();

    for _ in 0..9 {
        let mut out = RecycledAtom::new();
        target.replace_all_into(&pattern, &rhs, Some(&restrictions), None, &mut out);

        let mut out2 = RecycledAtom::new();
        out.expand_into(None, &mut out2);

        out2.replace_all_into(&lhs_zero_pat, &rhs_one, None, None, &mut out);

        out.replace_all_into(&lhs_one_pat, &rhs_one, None, None, &mut out2);

        target = out2;
    }

    assert_eq!(target.into_inner(), Atom::new_num(89));
}

#[test]
fn replace_once() {
    let expr = Atom::parse("f(z)*f(f(x))*f(y)").unwrap();
    let pat_expr = Atom::parse("f(x_)").unwrap();

    let rhs_expr = Atom::parse("g(x_)").unwrap();
    let rhs = rhs_expr.as_view().to_pattern();

    let pattern = pat_expr.as_view().to_pattern();

    let r: Vec<_> = expr
        .replace_iter(&pattern, &rhs, None, None)
        .into_iter()
        .collect();

    let res = [
        "g(z)*f(y)*f(f(x))",
        "f(z)*g(y)*f(f(x))",
        "f(z)*f(y)*g(f(x))",
        "f(z)*f(y)*f(g(x))",
    ];

    let res = res
        .iter()
        .map(|x| Atom::parse(x).unwrap())
        .collect::<Vec<_>>();

    assert_eq!(r, res);
}
