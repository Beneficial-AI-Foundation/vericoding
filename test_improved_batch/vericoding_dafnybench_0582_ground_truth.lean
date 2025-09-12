/-
  Port of vericoding_dafnybench_0582_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsSorted (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsSorted_spec (a : Array Int) (sorted : Bool) :=
  (h_0 : a.size > 0)
  : sorted ≤= ∀ i, j :: 0 ≤ i < j < a.size → a[i]! ≤ a[j]! ∧ !sorted → ∃ i, j :: 0 ≤ i < j < a.size ∧ a[i]! > a[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks