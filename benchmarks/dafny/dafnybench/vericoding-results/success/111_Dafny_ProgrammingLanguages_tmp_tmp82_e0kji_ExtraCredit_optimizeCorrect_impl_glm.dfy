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
lemma OptimizeCorrectness(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
{
  match e
  case Const(n) => 
    calc {
      eval(e, s);
      n;
      eval(Const(n), s);
    }
  case Var(x) =>
    calc {
      eval(e, s);
      if x in s then s[x] else -1;
      eval(Var(x), s);
    }
  case Plus(e1, e2) =>
    if e1 == Const(0) {
      calc {
        eval(e, s);
        eval(Plus(e1,e2), s);
        eval(e1, s) + eval(e2, s);
        0 + eval(e2, s);
        eval(e2, s);
        eval(optimize(e), s);
      }
    } else if e2 == Const(0) {
      calc {
        eval(e, s);
        eval(Plus(e1,e2), s);
        eval(e1, s) + eval(e2, s);
        eval(e1, s) + 0;
        eval(e1, s);
        eval(optimize(e), s);
      }
    } else if e1.Const? && e2.Const? {
      var n1 : int;
      match e1 {
        case Const(n) => n1 := n;
      }
      var n2 : int;
      match e2 {
        case Const(n) => n2 := n;
      }
      calc {
        eval(e, s);
        eval(Plus(e1,e2), s);
        eval(e1, s) + eval(e2, s);
        n1 + n2;
        eval(Const(n1+n2), s);
        eval(optimize(e), s);
      }
    } else {
      calc {
        eval(e, s);
        eval(Plus(e1,e2), s);
        eval(optimize(e), s);
      }
    }
  case Mult(e1, e2) =>
    if e1 == Const(0) {
      calc {
        eval(e, s);
        eval(Mult(e1,e2), s);
        eval(e1, s) * eval(e2, s);
        0 * eval(e2, s);
        0;
        eval(Const(0), s);
        eval(optimize(e), s);
      }
    } else if e2 == Const(0) {
      calc {
        eval(e, s);
        eval(Mult(e1,e2), s);
        eval(e1, s) * eval(e2, s);
        eval(e1, s) * 0;
        0;
        eval(Const(0), s);
        eval(optimize(e), s);
      }
    } else if e1 == Const(1) {
      calc {
        eval(e, s);
        eval(Mult(e1,e2), s);
        eval(e1, s) * eval(e2, s);
        1 * eval(e2, s);
        eval(e2, s);
        eval(optimize(e), s);
      }
    } else if e2 == Const(1) {
      calc {
        eval(e, s);
        eval(Mult(e1,e2), s);
        eval(e1, s) * eval(e2, s);
        eval(e1, s) * 1;
        eval(e1, s);
        eval(optimize(e), s);
      }
    } else if e1.Const? && e2.Const? {
      var n1 : int;
      match e1 {
        case Const(n) => n1 := n;
      }
      var n2 : int;
      match e2 {
        case Const(n) => n2 := n;
      }
      calc {
        eval(e, s);
        eval(Mult(e1,e2), s);
        eval(e1, s) * eval(e2, s);
        n1 * n2;
        eval(Const(n1*n2), s);
        eval(optimize(e), s);
      }
    } else {
      calc {
        eval(e, s);
        eval(Mult(e1,e2), s);
        eval(optimize(e), s);
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
  OptimizeCorrectness(e, s);
}
// </vc-code>

