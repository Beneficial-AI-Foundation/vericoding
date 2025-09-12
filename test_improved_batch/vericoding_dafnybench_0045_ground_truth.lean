/-
  Port of vericoding_dafnybench_0045_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def has_close_elements (numbers : seq<real>) (threshold : Float) : Bool :=
  sorry  -- TODO: implement function body

theorem has_close_elements_spec (numbers : seq<real>) (threshold : Float) (res : Bool) :=
  (h_0 : threshold ≥ 0.0)
  : res → ∃ i: Int, j: Int :: 0 ≤ i < |numbers| ∧ 0 ≤ j < |numbers| ∧ i ≠ j ∧ (if numbers[i]! - numbers[j]! < 0.0 then numbers[j]! - numbers[i]! else numbers[i]! - numbers[j]!) < threshold ∧ !res → (∀ i: Int, j: Int :: 1 ≤ i < |numbers| ∧ 0 ≤ j < i →  (if numbers[i]! - numbers[j]! < 0.0 then numbers[j]! - numbers[i]! else numbers[i]! - numbers[j]!) ≥ threshold)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks