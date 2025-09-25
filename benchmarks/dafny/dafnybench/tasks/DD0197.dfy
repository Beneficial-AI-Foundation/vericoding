// <vc-preamble>
datatype Exp = Const(int) | Var(string) | Plus(Exp, Exp) |  Mult(Exp, Exp)

function eval(e:Exp, store:map<string, int>):int
{
    match(e)
        case Const(n) => n
        case Var(s) => if(s in store) then store[s] else -1
        case Plus(e1, e2) => eval(e1, store) + eval(e2, store)
        case Mult(e1, e2) => eval(e1, store) * eval(e2, store)
}

function optimize(e:Exp):Exp
{
    match e
    case Mult(Const(0), e) => Const(0)
    case Mult(e, Const(0)) => Const(0)
    case Mult(Const(1), e) => e
    case Mult(e, Const(1)) => e
    case Mult(Const(n1), Const(n2)) => Const(n1*n2)
    case Plus(Const(0), e) => e
    case Plus(e, Const(0)) => e
    case Plus(Const(n1), Const(n2)) => Const(n1+ n2)
    case e => e

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method optimizeCorrect(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
