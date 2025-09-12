/-
  Port of dafny-learn_tmp_tmpn94ir40q_R01_assertions_Abs.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  : 0 ≤ y ∧ x < 0 → y == -x ∧ x ≥ 0 → y == x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks