/-
  Port of Correctness_tmp_tmpwqvg5q_4_HoareLogic_exam_GCD2.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def gcd (a : Nat) (b : Nat) : Nat :=
  sorry  -- TODO: implement function body

def GCD1 (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem GCD1_spec (a : Int) (b : Int) (r : Int) :=
  (h_0 : a > 0 ∧ b > 0)
  : gcd(a,b) == r
  := by
  sorry  -- TODO: implement proof

def GCD2 (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem GCD2_spec (a : Int) (b : Int) (r : Int) :=
  (h_0 : a > 0 ∧ b ≥ 0)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks