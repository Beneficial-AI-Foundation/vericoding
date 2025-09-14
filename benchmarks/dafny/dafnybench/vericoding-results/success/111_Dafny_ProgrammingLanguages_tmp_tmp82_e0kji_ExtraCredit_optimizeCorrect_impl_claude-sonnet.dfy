datatype Exp = Const(int) | Var(string) | Plus(Exp, Exp) |  Mult(Exp, Exp)

function eval(e:Exp, store:map<string, int>):int
{
    match(e)
        case Const(n) => n
        case Var(s) => if(s in store) then store[s] else -1
        case Plus(e1, e2) => eval(e1, store) + eval(e2, store)
        case Mult(e1, e2) => eval(e1, store) * eval(e2, store)
}

//fill this function in to make optimizeFeatures work
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

//as you write optimize this will become unproved
//you must write proof code so that Dafny can prove this

// <vc-helpers>
lemma optimizePreservesEval(e: Exp, s: map<string, int>)
    ensures eval(e, s) == eval(optimize(e), s)
{
    match e {
        case Const(n) => 
            assert optimize(e) == e;
        case Var(name) => 
            assert optimize(e) == e;
        case Plus(e1, e2) =>
            match e {
                case Plus(Const(0), e2) => 
                    assert eval(e, s) == 0 + eval(e2, s) == eval(e2, s);
                    assert optimize(e) == e2;
                case Plus(e1, Const(0)) => 
                    assert eval(e, s) == eval(e1, s) + 0 == eval(e1, s);
                    assert optimize(e) == e1;
                case Plus(Const(n1), Const(n2)) => 
                    assert eval(e, s) == n1 + n2;
                    assert optimize(e) == Const(n1 + n2);
                    assert eval(optimize(e), s) == n1 + n2;
                case _ => 
                    assert optimize(e) == e;
            }
        case Mult(e1, e2) =>
            match e {
                case Mult(Const(0), e2) => 
                    assert eval(e, s) == 0 * eval(e2, s) == 0;
                    assert optimize(e) == Const(0);
                    assert eval(optimize(e), s) == 0;
                case Mult(e1, Const(0)) => 
                    assert eval(e, s) == eval(e1, s) * 0 == 0;
                    assert optimize(e) == Const(0);
                    assert eval(optimize(e), s) == 0;
                case Mult(Const(1), e2) => 
                    assert eval(e, s) == 1 * eval(e2, s) == eval(e2, s);
                    assert optimize(e) == e2;
                case Mult(e1, Const(1)) => 
                    assert eval(e, s) == eval(e1, s) * 1 == eval(e1, s);
                    assert optimize(e) == e1;
                case Mult(Const(n1), Const(n2)) => 
                    assert eval(e, s) == n1 * n2;
                    assert optimize(e) == Const(n1 * n2);
                    assert eval(optimize(e), s) == n1 * n2;
                case _ => 
                    assert optimize(e) == e;
            }
    }
}
// </vc-helpers>

// <vc-spec>
method optimizeCorrect(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
// </vc-spec>
// <vc-code>
{
    optimizePreservesEval(e, s);
}
// </vc-code>

