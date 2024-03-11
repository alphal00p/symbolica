use symbolica::{
    fun,
    representations::{Atom, FunctionBuilder},
    state::State,
};

// fn zeros<'a>(ws:&'a Workspace,state:&'a State) -> Vec<Expr<'a>>{

//     let zeroatom = ws.new_num(0).to_owned();
//     let zero = zeroatom.builder(&state, ws).to_owned();
//     vec![zero;3]
// } 

fn main() {
    let x = Atom::parse("x").unwrap();
    let y = Atom::parse("y").unwrap();
    let f_id = State::get_or_insert_fn("f", None).unwrap();

    let f = fun!(f_id, x, y, Atom::new_num(2));

    let xb = (-(&y + &x + 2) * &y * 6).npow(5) / &y * &f / 4;

    println!("{}", xb);
}
