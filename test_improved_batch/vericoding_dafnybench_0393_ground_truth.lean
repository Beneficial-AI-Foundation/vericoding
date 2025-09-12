/-
  Port of vericoding_dafnybench_0393_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  := by
  sorry  -- TODO: implement proof


  (h_0 : Sorted(q))
  : left ≤ right ≤ |q| ∧ ∀ i :: 0 ≤ i < left → q[i]! < key ∧ ∀ i :: left ≤ i < right → q[i]! == key ∧ ∀ i :: right ≤ i < |q| → q[i]! > key
  := by
  sorry  -- TODO: implement proof


  (h_0 : Sorted(q))
  (h_1 : 0 ≤ lowerBound ≤ upperBound ≤ |q|)
  (h_2 : RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer))
  (h_3 : RangeSatisfiesComparer(q, key, upperBound, |q|, comparer))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks