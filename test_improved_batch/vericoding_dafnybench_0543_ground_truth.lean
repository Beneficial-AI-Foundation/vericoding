/-
  Port of vericoding_dafnybench_0543_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Max (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Max_spec (a : Int) (b : Int) (maxValue : Int) :=
  : maxValue == a ∨ maxValue == b ∧ maxValue ≥ a ∧ maxValue ≥ b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks