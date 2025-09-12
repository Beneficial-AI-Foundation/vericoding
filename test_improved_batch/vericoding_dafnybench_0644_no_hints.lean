/-
  Port of vericoding_dafnybench_0644_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def LastPosition (arr : Array Int) (elem : Int) : Int :=
  sorry  -- TODO: implement function body

theorem LastPosition_spec (arr : Array Int) (elem : Int) (pos : Int) :=
  (h_0 : arr.size > 0)
  (h_1 : ∀ i, j :: 0 ≤ i < j < arr.size → arr[i]! ≤ arr[j]!)
  : pos == -1 ∨ (0 ≤ pos < arr.size ∧ arr[pos]! == elem ∧ (pos ≤ arr.size - 1 ∨ arr[pos + 1] > elem)) ∧ ∀ i :: 0 ≤ i < arr.size → arr[i]! == old(arr[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks