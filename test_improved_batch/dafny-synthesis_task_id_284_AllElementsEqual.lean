/-
  Port of dafny-synthesis_task_id_284_AllElementsEqual.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def AllElementsEqual (a : Array Int) (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem AllElementsEqual_spec (a : Array Int) (n : Int) (result : Bool) :=
  (h_0 : a ≠ null)
  : result → ∀ i :: 0 ≤ i < a.size → a[i]! == n ∧ !result → ∃ i, 0 ≤ i < a.size ∧ a[i]! ≠ n
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks