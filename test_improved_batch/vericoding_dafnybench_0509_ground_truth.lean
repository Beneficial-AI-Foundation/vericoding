/-
  Port of vericoding_dafnybench_0509_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MaxDifference (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem MaxDifference_spec (a : Array Int) (diff : Int) :=
  (h_0 : a.size > 1)
  : ∀ i, j :: 0 ≤ i < a.size ∧ 0 ≤ j < a.size → a[i]! - a[j]! ≤ diff
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks