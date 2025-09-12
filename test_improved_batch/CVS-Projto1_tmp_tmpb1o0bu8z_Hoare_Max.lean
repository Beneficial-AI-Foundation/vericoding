/-
  Port of CVS-Projto1_tmp_tmpb1o0bu8z_Hoare_Max.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def add (l : List<int>) : Int :=
  match l case Nil => 0 case Cons(x, xs) => x + add(xs)

def Max (x : Nat) (y : Nat) : Nat :=
  sorry  -- TODO: implement function body

theorem Max_spec (x : Nat) (y : Nat) (r : Nat) :=
  : (r ≥ x ∧ r ≥y) ∧ (r == x ∨ r == y)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks