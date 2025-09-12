/-
  Port of vericoding_dafnybench_0448_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def BinarySearch (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (a : Array Int) (key : Int) (result : Int) :=
  (h_0 : ∀ i, j :: 0 ≤ i < j < a.size → a[i]! ≤ a[j]!;)
  : -1 ≤ result < a.size; ∧ 0 ≤ result → a[result]! == key; ∧ result == -1 → ∀ i :: 0 ≤ i < a.size → a[i]! ≠ key;
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  (h_0 : ∀ i, j :: 0 ≤ i < j < a.size → a[i]! ≤ a[j]!;)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks