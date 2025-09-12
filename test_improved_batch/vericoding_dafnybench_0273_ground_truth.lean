/-
  Port of vericoding_dafnybench_0273_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def problem3 (m : Int) (X : Int) : Int :=
  sorry  -- TODO: implement function body

theorem problem3_spec (m : Int) (X : Int) (r : Int) :=
  (h_0 : X ≥ 0 ∧ (2*m == 1 - X ∨ m == X + 3))
  : r == X
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks