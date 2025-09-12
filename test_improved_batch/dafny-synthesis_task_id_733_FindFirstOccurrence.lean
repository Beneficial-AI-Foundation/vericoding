/-
  Port of dafny-synthesis_task_id_733_FindFirstOccurrence.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindFirstOccurrence (arr : Array Int) (target : Int) : Int :=
  sorry  -- TODO: implement function body

theorem FindFirstOccurrence_spec (arr : Array Int) (target : Int) (index : Int) :=
  (h_0 : arr ≠ null)
  (h_1 : ∀ i, j :: 0 ≤ i < j < arr.size → arr[i]! ≤ arr[j]!)
  : 0 ≤ index < arr.size → arr[index]! == target ∧ index == -1 → ∀ i :: 0 ≤ i < arr.size → arr[i]! ≠ target ∧ ∀ i :: 0 ≤ i < arr.size → arr[i]! == old(arr[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks