/-
  Port of vericoding_dafnybench_0305_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindMax (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem FindMax_spec (a : Array Int) (max : Int) :=
  (h_0 : a ≠ null ∧ a.size > 0;)
  : 0 ≤ max < a.size; ∧ ∀ x :: 0 ≤ x < a.size → a[max]! ≥ a[x]!;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks