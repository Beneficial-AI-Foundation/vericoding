use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum Exp {
    Const(int),
    Var(String),
    Plus(Box<Exp>, Box<Exp>),
    Mult(Box<Exp>, Box<Exp>),
}

pub spec fn eval(e: Exp, store: Map<String, int>) -> int {
    match e {
        Exp::Const(n) => n,
        Exp::Var(s) => if store.dom().contains(s) { store[s] } else { -1 },
        Exp::Plus(e1, e2) => eval(*e1, store) + eval(*e2, store),
        Exp::Mult(e1, e2) => eval(*e1, store) * eval(*e2, store),
    }
}

pub spec fn optimize(e: Exp) -> Exp {
    match e {
        Exp::Mult(e1, e2) => match (*e1, *e2) {
            (Exp::Const(0), _) => Exp::Const(0),
            (_, Exp::Const(0)) => Exp::Const(0),
            (Exp::Const(1), e) => e,
            (e, Exp::Const(1)) => e,
            (Exp::Const(n1), Exp::Const(n2)) => Exp::Const(n1 * n2),
            _ => e,
        },
        Exp::Plus(e1, e2) => match (*e1, *e2) {
            (Exp::Const(0), e) => e,
            (e, Exp::Const(0)) => e,
            (Exp::Const(n1), Exp::Const(n2)) => Exp::Const(n1 + n2),
            _ => e,
        },
        _ => e,
    }
}

pub fn optimizeCorrect(e: Exp, s: Map<String, int>)
    ensures eval(e, s) == eval(optimize(e), s)
{
}

pub fn optimizeFeatures() {
}

}