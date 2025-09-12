/-
  Port of vericoding_dafnybench_0144_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def eval (e : Exp) (store : map<string) int> : Int :=
  match(e) case Const(n) => n case Var(s) => if(s in store) then store[s]! else -1 case Plus(e1, e2) => eval(e1, store) + eval(e2, store) case Mult(e1, e2) => eval(e1, store) * eval(e2, store)

def optimize (e : Exp) : Exp :=
  match e case Mult(Const(0), e) => Const(0) case Mult(e, Const(0)) => Const(0) case Mult(Const(1), e) => e case Mult(e, Const(1)) => e case Mult(Const(n1), Const(n2)) => Const(n1*n2) case Plus(Const(0), e) => e case Plus(e, Const(0)) => e case Plus(Const(n1), Const(n2)) => Const(n1+ n2) case e => e


  : eval(e,s) == eval(optimize(e), s)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks