//ATOM
datatype Exp = Const(int) | Var(string) | Plus(Exp, Exp) |  Mult(Exp, Exp)


//ATOM

function eval(e:Exp, store:map<string, int>):int
{
	match(e)
		case Const(n) => n
		case Var(s) => if(s in store) then store[s] else -1
		case Plus(e1, e2) => eval(e1, store) + eval(e2, store)
		case Mult(e1, e2) => eval(e1, store) * eval(e2, store)
}


//ATOM

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


//IMPL

//as you write optimize this will become unproved
//you must write proof code so that Dafny can prove this
method optimizeCorrect(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
{
	match e {
		case Const(n) => 
			// optimize(Const(n)) == Const(n), so eval is the same
		case Var(str) => 
			// optimize(Var(str)) == Var(str), so eval is the same
		case Plus(e1, e2) => 
			match e1 {
				case Const(0) => 
					// optimize(Plus(Const(0), e2)) == e2
					// eval(Plus(Const(0), e2), s) == eval(Const(0), s) + eval(e2, s) == 0 + eval(e2, s) == eval(e2, s)
				case _ => 
					match e2 {
						case Const(0) => 
							// optimize(Plus(e1, Const(0))) == e1
							// eval(Plus(e1, Const(0)), s) == eval(e1, s) + eval(Const(0), s) == eval(e1, s) + 0 == eval(e1, s)
						case Const(n2) => 
							match e1 {
								case Const(n1) => 
									// optimize(Plus(Const(n1), Const(n2))) == Const(n1 + n2)
									// eval(Plus(Const(n1), Const(n2)), s) == eval(Const(n1), s) + eval(Const(n2), s) == n1 + n2 == eval(Const(n1 + n2), s)
								case _ => 
									// optimize(Plus(e1, Const(n2))) == Plus(e1, Const(n2)) when e1 is not Const(0) and n2 is not 0
							}
						case _ => 
							// optimize(Plus(e1, e2)) == Plus(e1, e2) when no optimization applies
					}
			}
		case Mult(e1, e2) => 
			match e1 {
				case Const(0) => 
					// optimize(Mult(Const(0), e2)) == Const(0)
					// eval(Mult(Const(0), e2), s) == eval(Const(0), s) * eval(e2, s) == 0 * eval(e2, s) == 0 == eval(Const(0), s)
				case Const(1) => 
					// optimize(Mult(Const(1), e2)) == e2
					// eval(Mult(Const(1), e2), s) == eval(Const(1), s) * eval(e2, s) == 1 * eval(e2, s) == eval(e2, s)
				case _ => 
					match e2 {
						case Const(0) => 
							// optimize(Mult(e1, Const(0))) == Const(0)
							// eval(Mult(e1, Const(0)), s) == eval(e1, s) * eval(Const(0), s) == eval(e1, s) * 0 == 0 == eval(Const(0), s)
						case Const(1) => 
							// optimize(Mult(e1, Const(1))) == e1
							// eval(Mult(e1, Const(1)), s) == eval(e1, s) * eval(Const(1), s) == eval(e1, s) * 1 == eval(e1, s)
						case Const(n2) => 
							match e1 {
								case Const(n1) => 
									// optimize(Mult(Const(n1), Const(n2))) == Const(n1 * n2)
									// eval(Mult(Const(n1), Const(n2)), s) == eval(Const(n1), s) * eval(Const(n2), s) == n1 * n2 == eval(Const(n1 * n2), s)
								case _ => 
									// optimize(Mult(e1, Const(n2))) == Mult(e1, Const(n2)) when e1 is not Const(0) or Const(1) and n2 is not 0 or 1
							}
						case _ => 
							// optimize(Mult(e1, e2)) == Mult(e1, e2) when no optimization applies
					}
			}
	}
}