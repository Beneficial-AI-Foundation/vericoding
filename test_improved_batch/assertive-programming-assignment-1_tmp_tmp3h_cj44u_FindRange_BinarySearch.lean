/-
  Port of assertive-programming-assignment-1_tmp_tmp3h_cj44u_FindRange_BinarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : Sorted(q))
  (h_1 : 0 ≤ lowerBound ≤ upperBound ≤ |q|)
  (h_2 : RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer))
  (h_3 : RangeSatisfiesComparer(q, key, upperBound, |q|, comparer))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks