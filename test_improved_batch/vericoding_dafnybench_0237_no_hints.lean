/-
  Port of vericoding_dafnybench_0237_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def BinarySearch (arr : Array Int) (target : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (arr : Array Int) (target : Int) (index : Int) :=
  (h_0 : distinct(arr))
  (h_1 : sorted(arr))
  : -1 ≤ index < arr.size ∧ index == -1 → not_found(arr, target) ∧ index ≠ -1 → found(arr, target, index)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks