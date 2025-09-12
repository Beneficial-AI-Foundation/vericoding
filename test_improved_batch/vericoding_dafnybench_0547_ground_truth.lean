/-
  Port of vericoding_dafnybench_0547_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MedianOfThree (a : Int) (b : Int) (c : Int) : Int :=
  sorry  -- TODO: implement function body

theorem MedianOfThree_spec (a : Int) (b : Int) (c : Int) (median : Int) :=
  : median == a ∨ median == b ∨ median == c ∧ (median ≥ a ∧ median ≤ b) ∨ (median ≥ b ∧ median ≤ a) ∨ (median ≥ a ∧ median ≤ c) ∨ (median ≥ c ∧ median ≤ a) ∨ (median ≥ b ∧ median ≤ c) ∨ (median ≥ c ∧ median ≤ b)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks