/-
  Port of vericoding_dafnybench_0565_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CalculateLoss (costPrice : Int) (sellingPrice : Int) : Int :=
  sorry  -- TODO: implement function body

theorem CalculateLoss_spec (costPrice : Int) (sellingPrice : Int) (loss : Int) :=
  (h_0 : costPrice ≥ 0 ∧ sellingPrice ≥ 0)
  : (costPrice > sellingPrice → loss == costPrice - sellingPrice) ∧ (costPrice ≤ sellingPrice → loss == 0)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks