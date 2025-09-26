import Mathlib
-- <vc-preamble>
@[reducible, simp]
def splitAndAppend_precond (list : Array Int) (n : Nat) :=
  list.size > 0 ∧ 0 < n ∧ n < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers are required for this verification task.
-- </vc-helpers>

-- <vc-definitions>
def splitAndAppend (list : Array Int) (n : Nat) (h_precond : splitAndAppend_precond (list) (n)) : Array Int :=
  (list.toList.drop n ++ list.toList.take n).toArray
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def splitAndAppend_postcond (list : Array Int) (n : Nat) (new_list: Array Int) (h_precond : splitAndAppend_precond (list) (n)) :=
  new_list.toList = (list.toList.drop n) ++ (list.toList.take n)

theorem splitAndAppend_spec_satisfied (list: Array Int) (n: Nat) (h_precond : splitAndAppend_precond (list) (n)) :
    splitAndAppend_postcond (list) (n) (splitAndAppend (list) (n) h_precond) h_precond := by
  unfold splitAndAppend_postcond
  simp [splitAndAppend]
-- </vc-theorems>
