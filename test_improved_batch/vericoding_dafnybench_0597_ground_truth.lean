/-
  Port of vericoding_dafnybench_0597_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FirstEvenOddDifference (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem FirstEvenOddDifference_spec (a : Array Int) (diff : Int) :=
  (h_0 : a.size ≥ 2)
  (h_1 : ∃ i, 0 ≤ i < a.size ∧ IsEven(a[i]!))
  (h_2 : ∃ i, 0 ≤ i < a.size ∧ IsOdd(a[i]!))
  : ∃ i, j :: 0 ≤ i < a.size ∧ 0 ≤ j < a.size ∧ IsEven(a[i]!) ∧ IsOdd(a[j]!) ∧ diff == a[i]! - a[j]! ∧
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks