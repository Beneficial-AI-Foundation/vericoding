/-
  Port of vericoding_dafnybench_0629_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsMinHeap (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsMinHeap_spec (a : Array Int) (result : Bool) :=
  (h_0 : a ≠ null)
  : result → ∀ i :: 0 ≤ i < a.size / 2 → a[i]! ≤ a[2*i + 1] ∧ (2*i + 2 == a.size ∨ a[i]! ≤ a[2*i + 2]) ∧ !result → ∃ i, 0 ≤ i < a.size / 2 ∧ (a[i]! > a[2*i + 1] ∨ (2*i + 2 ≠ a.size ∧ a[i]! > a[2*i + 2]))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks