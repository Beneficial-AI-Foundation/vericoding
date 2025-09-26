import Mathlib
-- <vc-preamble>
/- Recursive function to compute sum of list elements -/
def sumTo (arr : List Int) : Int :=
  match arr with
  | [] => 0
  | _ :: xs => sumTo xs + arr.getLast!
  termination_by arr.length

@[reducible, simp]
def sumRangeList_precond (arr : Array Int) (start : Nat) (endVal : Nat) : Prop :=
  start ≤ endVal ∧ endVal < arr.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper definitions required for this file.
-- </vc-helpers>

-- <vc-definitions>
def sumRangeList (arr : Array Int) (start : Nat) (endVal : Nat) (h_precond : sumRangeList_precond arr start endVal) : Int :=
  sumTo (arr.toList.drop start |>.take (endVal + 1 - start))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumRangeList_postcond (arr : Array Int) (start : Nat) (endVal : Nat) (sum : Int) (h_precond : sumRangeList_precond arr start endVal) : Prop :=
  sumTo (arr.toList.drop start |>.take (endVal + 1 - start)) = sum

theorem sumRangeList_spec_satisfied (arr : Array Int) (start : Nat) (endVal : Nat) (h_precond : sumRangeList_precond arr start endVal) :
    sumRangeList_postcond arr start endVal (sumRangeList arr start endVal h_precond) h_precond := by
  simp [sumRangeList_postcond, sumRangeList]
-- </vc-theorems>
