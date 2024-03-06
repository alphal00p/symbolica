use symbolica::{id::AtomTreeIterator, representations::Atom, state::State};

fn main() {
    let mut state = State::get_global_state().write().unwrap();

    let expr: Atom = Atom::parse("f(z)*f(f(x),z)*f(y)", &mut state).unwrap();

    println!("> Tree walk of {}:", expr);

    for (loc, view) in AtomTreeIterator::new(expr.as_view()) {
        println!("\tAtom at location {:?}: {}", loc, view);
    }
}
