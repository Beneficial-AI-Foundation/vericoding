/-
  Port of CVS-Projto1_tmp_tmpb1o0bu8z_Hoare_Fib.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def add (l : List<int>) : Int :=
  match l case Nil => 0 case Cons(x, xs) => x + add(xs)

def Fib (n : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem Fib_spec (n : Nat) (r : Nat) :=
  : r == fib(n)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks