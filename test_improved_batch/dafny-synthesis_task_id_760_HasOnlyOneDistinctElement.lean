/-
  Port of dafny-synthesis_task_id_760_HasOnlyOneDistinctElement.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def HasOnlyOneDistinctElement (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem HasOnlyOneDistinctElement_spec (a : Array Int) (result : Bool) :=
  (h_0 : a ≠ null)
  : result → ∀ i, j :: 0 ≤ i < a.size ∧ 0 ≤ j < a.size → a[i]! == a[j]! ∧ !result → ∃ i, j :: 0 ≤ i < a.size ∧ 0 ≤ j < a.size ∧ a[i]! ≠ a[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks