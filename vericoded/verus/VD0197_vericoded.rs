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

//fill this function in to make optimizeFeatures work
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

//as you write optimize this will become unproved
//you must write proof code so that Verus can prove this

// <vc-helpers>
proof fn optimize_mult_correct(e1: Box<Exp>, e2: Box<Exp>, s: Map<String, int>)
    ensures eval(Exp::Mult(e1, e2), s) == eval(optimize(Exp::Mult(e1, e2)), s)
{
    let mult_exp = Exp::Mult(e1, e2);
    match (*e1, *e2) {
        (Exp::Const(n1), _) if n1 == 0 => {
            assert(eval(*e1, s) == n1);
            assert(eval(mult_exp, s) == eval(*e1, s) * eval(*e2, s));
            assert(eval(mult_exp, s) == n1 * eval(*e2, s));
            assert(eval(mult_exp, s) == 0 * eval(*e2, s));
            assert(eval(mult_exp, s) == 0);
            assert(optimize(mult_exp) == Exp::Const(0));
            assert(eval(optimize(mult_exp), s) == 0);
        },
        (_, Exp::Const(n2)) if n2 == 0 => {
            assert(eval(*e2, s) == n2);
            assert(eval(mult_exp, s) == eval(*e1, s) * eval(*e2, s));
            assert(eval(mult_exp, s) == eval(*e1, s) * n2);
            assert(eval(mult_exp, s) == eval(*e1, s) * 0);
            assert(eval(mult_exp, s) == 0);
            assert(optimize(mult_exp) == Exp::Const(0));
            assert(eval(optimize(mult_exp), s) == 0);
        },
        (Exp::Const(n1), e2_inner) if n1 == 1 => {
            assert(eval(*e1, s) == n1);
            assert(*e2 == e2_inner);
            assert(eval(mult_exp, s) == eval(*e1, s) * eval(*e2, s));
            assert(eval(mult_exp, s) == n1 * eval(*e2, s));
            assert(eval(mult_exp, s) == 1 * eval(*e2, s));
            assert(eval(mult_exp, s) == eval(*e2, s));
            assert(optimize(mult_exp) == e2_inner);
            assert(eval(optimize(mult_exp), s) == eval(e2_inner, s));
            assert(eval(e2_inner, s) == eval(*e2, s));
        },
        (e1_inner, Exp::Const(n2)) if n2 == 1 => {
            assert(eval(*e2, s) == n2);
            assert(*e1 == e1_inner);
            assert(eval(mult_exp, s) == eval(*e1, s) * eval(*e2, s));
            assert(eval(mult_exp, s) == eval(*e1, s) * n2);
            assert(eval(mult_exp, s) == eval(*e1, s) * 1);
            assert(eval(mult_exp, s) == eval(*e1, s));
            assert(optimize(mult_exp) == e1_inner);
            assert(eval(optimize(mult_exp), s) == eval(e1_inner, s));
            assert(eval(e1_inner, s) == eval(*e1, s));
        },
        (Exp::Const(n1), Exp::Const(n2)) => {
            assert(eval(*e1, s) == n1);
            assert(eval(*e2, s) == n2);
            assert(eval(mult_exp, s) == eval(*e1, s) * eval(*e2, s));
            assert(eval(mult_exp, s) == n1 * n2);
            assert(optimize(mult_exp) == Exp::Const(n1 * n2));
            assert(eval(optimize(mult_exp), s) == n1 * n2);
        },
        _ => {
            assert(optimize(mult_exp) == mult_exp);
        }
    }
}

proof fn optimize_plus_correct(e1: Box<Exp>, e2: Box<Exp>, s: Map<String, int>)
    ensures eval(Exp::Plus(e1, e2), s) == eval(optimize(Exp::Plus(e1, e2)), s)
{
    let plus_exp = Exp::Plus(e1, e2);
    match (*e1, *e2) {
        (Exp::Const(n1), e2_inner) if n1 == 0 => {
            assert(eval(*e1, s) == n1);
            assert(*e2 == e2_inner);
            assert(eval(plus_exp, s) == eval(*e1, s) + eval(*e2, s));
            assert(eval(plus_exp, s) == n1 + eval(*e2, s));
            assert(eval(plus_exp, s) == 0 + eval(*e2, s));
            assert(eval(plus_exp, s) == eval(*e2, s));
            assert(optimize(plus_exp) == e2_inner);
            assert(eval(optimize(plus_exp), s) == eval(e2_inner, s));
            assert(eval(e2_inner, s) == eval(*e2, s));
        },
        (e1_inner, Exp::Const(n2)) if n2 == 0 => {
            assert(eval(*e2, s) == n2);
            assert(*e1 == e1_inner);
            assert(eval(plus_exp, s) == eval(*e1, s) + eval(*e2, s));
            assert(eval(plus_exp, s) == eval(*e1, s) + n2);
            assert(eval(plus_exp, s) == eval(*e1, s) + 0);
            assert(eval(plus_exp, s) == eval(*e1, s));
            assert(optimize(plus_exp) == e1_inner);
            assert(eval(optimize(plus_exp), s) == eval(e1_inner, s));
            assert(eval(e1_inner, s) == eval(*e1, s));
        },
        (Exp::Const(n1), Exp::Const(n2)) => {
            assert(eval(*e1, s) == n1);
            assert(eval(*e2, s) == n2);
            assert(eval(plus_exp, s) == eval(*e1, s) + eval(*e2, s));
            assert(eval(plus_exp, s) == n1 + n2);
            assert(optimize(plus_exp) == Exp::Const(n1 + n2));
            assert(eval(optimize(plus_exp), s) == n1 + n2);
        },
        _ => {
            assert(optimize(plus_exp) == plus_exp);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn optimize_correct(e: Exp, s: Map<String, int>)
    ensures eval(e, s) == eval(optimize(e), s)
// </vc-spec>
// <vc-code>
{
    match e {
        Exp::Const(_) => {},
        Exp::Var(_) => {},
        Exp::Plus(e1, e2) => {
            proof {
                optimize_plus_correct(e1, e2, s);
            }
        },
        Exp::Mult(e1, e2) => {
            proof {
                optimize_mult_correct(e1, e2, s);
            }
        }
    }
}
// </vc-code>

fn main() {}

}