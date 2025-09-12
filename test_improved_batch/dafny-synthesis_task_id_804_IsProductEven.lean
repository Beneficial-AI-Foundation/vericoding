/-
  Port of dafny-synthesis_task_id_804_IsProductEven.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsProductEven (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsProductEven_spec (a : Array Int) (result : Bool) :=
  : result <→ ∃ i, 0 ≤ i < a.size ∧ IsEven(a[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks