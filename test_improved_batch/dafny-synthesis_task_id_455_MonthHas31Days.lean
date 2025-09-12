/-
  Port of dafny-synthesis_task_id_455_MonthHas31Days.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MonthHas31Days (month : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem MonthHas31Days_spec (month : Int) (result : Bool) :=
  (h_0 : 1 ≤ month ≤ 12)
  : result <→ month in {1, 3, 5, 7, 8, 10, 12}
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks