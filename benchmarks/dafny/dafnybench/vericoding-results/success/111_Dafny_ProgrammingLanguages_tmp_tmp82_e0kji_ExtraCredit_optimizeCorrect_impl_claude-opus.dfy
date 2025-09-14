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
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method optimizeCorrect(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
// </vc-spec>
// <vc-code>
{
  match e {
    case Const(n) => 
      // optimize(Const(n)) = Const(n)
      // eval(Const(n), s) = n = eval(Const(n), s)
      
    case Var(x) =>
      // optimize(Var(x)) = Var(x)
      // eval(Var(x), s) = eval(Var(x), s)
      
    case Plus(e1, e2) =>
      // Need to consider all optimization cases for Plus
      match e1 {
        case Const(0) =>
          // optimize(Plus(Const(0), e2)) = e2
          // eval(Plus(Const(0), e2), s) = 0 + eval(e2, s) = eval(e2, s)
          
        case _ =>
          match e2 {
            case Const(0) =>
              // optimize(Plus(e1, Const(0))) = e1
              // eval(Plus(e1, Const(0)), s) = eval(e1, s) + 0 = eval(e1, s)
              
            case _ =>
              match (e1, e2) {
                case (Const(n1), Const(n2)) =>
                  // optimize(Plus(Const(n1), Const(n2))) = Const(n1 + n2)
                  // eval(Plus(Const(n1), Const(n2)), s) = n1 + n2 = eval(Const(n1 + n2), s)
                  
                case _ =>
                  // No optimization applies
                  // optimize(Plus(e1, e2)) = Plus(e1, e2)
                  // eval(Plus(e1, e2), s) = eval(Plus(e1, e2), s)
              }
          }
      }
      
    case Mult(e1, e2) =>
      // Need to consider all optimization cases for Mult
      match e1 {
        case Const(0) =>
          // optimize(Mult(Const(0), e2)) = Const(0)
          // eval(Mult(Const(0), e2), s) = 0 * eval(e2, s) = 0 = eval(Const(0), s)
          
        case Const(1) =>
          // optimize(Mult(Const(1), e2)) = e2
          // eval(Mult(Const(1), e2), s) = 1 * eval(e2, s) = eval(e2, s)
          
        case _ =>
          match e2 {
            case Const(0) =>
              // optimize(Mult(e1, Const(0))) = Const(0)
              // eval(Mult(e1, Const(0)), s) = eval(e1, s) * 0 = 0 = eval(Const(0), s)
              
            case Const(1) =>
              // optimize(Mult(e1, Const(1))) = e1
              // eval(Mult(e1, Const(1)), s) = eval(e1, s) * 1 = eval(e1, s)
              
            case _ =>
              match (e1, e2) {
                case (Const(n1), Const(n2)) =>
                  // optimize(Mult(Const(n1), Const(n2))) = Const(n1 * n2)
                  // eval(Mult(Const(n1), Const(n2)), s) = n1 * n2 = eval(Const(n1 * n2), s)
                  
                case _ =>
                  // No optimization applies
                  // optimize(Mult(e1, e2)) = Mult(e1, e2)
                  // eval(Mult(e1, e2), s) = eval(Mult(e1, e2), s)
              }
          }
      }
  }
}
// </vc-code>

