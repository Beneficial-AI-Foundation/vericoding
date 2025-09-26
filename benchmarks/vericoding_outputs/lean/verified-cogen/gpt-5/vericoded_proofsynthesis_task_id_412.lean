import Mathlib
-- <vc-preamble>
@[reducible, simp]
def removeOdds_precond (arr : Array UInt32) := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed.
-- </vc-helpers>

-- <vc-definitions>
def removeOdds (arr : Array UInt32) (h_precond : removeOdds_precond (arr)) : Array UInt32 :=
  (arr.toList.filter (fun x => x % 2 = 0)).toArray
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeOdds_postcond (arr : Array UInt32) (even_list: Array UInt32) (h_precond : removeOdds_precond (arr)) :=
  even_list.toList = (arr.toList.filter (fun x => x % 2 = 0))

theorem removeOdds_spec_satisfied (arr: Array UInt32) (h_precond : removeOdds_precond (arr)) :
    removeOdds_postcond (arr) (removeOdds (arr) h_precond) h_precond := by
  simp [removeOdds_postcond, removeOdds]
-- </vc-theorems>
