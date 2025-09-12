/-
  Port of vericoding_dafnybench_0583_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def RemoveDuplicates (a : Array Int) : seq<int> :=
  sorry  -- TODO: implement function body

theorem RemoveDuplicates_spec (a : Array Int) (result : seq<int>) :=
  (h_0 : a ≠ null)
  : ∀ x :: x in result <→ ∃ i, 0 ≤ i < a.size ∧ a[i]! == x ∧ ∀ i, j :: 0 ≤ i < j < |result| → result[i]! ≠ result[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks