pub enum Exp {
    Const(int),
    Var(String),
    Plus(Box<Exp>, Box<Exp>),
    Mult(Box<Exp>, Box<Exp>),
}

pub fn eval(e: Exp, store: Map<String, int>) -> int
{
    match e {
        Exp::Const(n) => n,
        Exp::Var(s) => if store.contains_key(s) { store[s] } else { -1 },
        Exp::Plus(e1, e2) => eval(*e1, store) + eval(*e2, store),
        Exp::Mult(e1, e2) => eval(*e1, store) * eval(*e2, store),
    }
}

pub fn optimize(e: Exp) -> Exp
{
    match e {
        Exp::Mult(box Exp::Const(0), e) => Exp::Const(0),
        Exp::Mult(e, box Exp::Const(0)) => Exp::Const(0),
        Exp::Mult(box Exp::Const(1), e) => e,
        Exp::Mult(e, box Exp::Const(1)) => e,
        Exp::Mult(box Exp::Const(n1), box Exp::Const(n2)) => Exp::Const(n1 * n2),
        Exp::Plus(box Exp::Const(0), e) => e,
        Exp::Plus(e, box Exp::Const(0)) => e,
        Exp::Plus(box Exp::Const(n1), box Exp::Const(n2)) => Exp::Const(n1 + n2),
        e => e,
    }
}

pub fn optimizeCorrect(e: Exp, s: Map<String, int>)
    ensures(eval(e, s) == eval(optimize(e), s))
{
}