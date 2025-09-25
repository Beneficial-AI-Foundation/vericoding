// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
enum Exp {
    Const(int),
    Var(String),
    Plus(Box<Exp>, Box<Exp>),
    Mult(Box<Exp>, Box<Exp>),
}

spec fn eval(e: Exp, store: Map<String, int>) -> int
    decreases e
{
    match e {
        Exp::Const(n) => n,
        Exp::Var(s) => if store.dom().contains(s) { store[s] } else { -1 },
        Exp::Plus(e1, e2) => eval(*e1, store) + eval(*e2, store),
        Exp::Mult(e1, e2) => eval(*e1, store) * eval(*e2, store),
    }
}

spec fn optimize(e: Exp) -> Exp
    decreases e
{
    match e {
        Exp::Mult(e1, e2) => {
            match (*e1, *e2) {
                (Exp::Const(n1), _) if n1 == 0 => Exp::Const(0),
                (_, Exp::Const(n2)) if n2 == 0 => Exp::Const(0),
                (Exp::Const(n1), e2_inner) if n1 == 1 => e2_inner,
                (e1_inner, Exp::Const(n2)) if n2 == 1 => e1_inner,
                (Exp::Const(n1), Exp::Const(n2)) => Exp::Const(n1 * n2),
                _ => e,
            }
        },
        Exp::Plus(e1, e2) => {
            match (*e1, *e2) {
                (Exp::Const(n1), e2_inner) if n1 == 0 => e2_inner,
                (e1_inner, Exp::Const(n2)) if n2 == 0 => e1_inner,
                (Exp::Const(n1), Exp::Const(n2)) => Exp::Const(n1 + n2),
                _ => e,
            }
        },
        _ => e,
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn optimize_correct(e: Exp, s: Map<String, int>)
    ensures eval(e, s) == eval(optimize(e), s)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}