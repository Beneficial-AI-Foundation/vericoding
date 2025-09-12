/-
  Port of dafny-synthesis_task_id_404_Min.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Min (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Min_spec (a : Int) (b : Int) (minValue : Int) :=
  : minValue == a ∨ minValue == b ∧ minValue ≤ a ∧ minValue ≤ b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks