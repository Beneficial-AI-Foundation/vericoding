/-
  Port of dafny-synthesis_task_id_807_FindFirstOdd.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindFirstOdd (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem FindFirstOdd_spec (a : Array Int) (found : Bool) :=
  (h_0 : a ≠ null)
  : !found → ∀ i :: 0 ≤ i < a.size → !IsOdd(a[i]!) ∧ found → 0 ≤ index < a.size ∧ IsOdd(a[index]!) ∧ ∀ i :: 0 ≤ i < index → !IsOdd(a[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks