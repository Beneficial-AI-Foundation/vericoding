/-
  Port of CVS-Projto1_tmp_tmpb1o0bu8z_Hoare_m1.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def add (l : List<int>) : Int :=
  match l case Nil => 0 case Cons(x, xs) => x + add(xs)

def m1 (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem m1_spec (x : Int) (y : Int) (z : Int) :=
  (h_0 : 0 < x < y)
  : z ≥ 0 ∧ z ≤ y ∧ z ≠ x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks