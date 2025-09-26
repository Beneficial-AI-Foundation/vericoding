import Mathlib
-- <vc-preamble>
@[reducible, simp]
def findEvenNumbers_precond (arr : Array Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this verification condition.
-- </vc-helpers>

-- <vc-definitions>
def findEvenNumbers (arr : Array Nat) (h_precond : findEvenNumbers_precond (arr)) : Array Nat :=
  Array.mk (arr.toList.filter (fun x => x % 2 = 0))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Nat) (even_numbers: Array Nat) (h_precond : findEvenNumbers_precond (arr)) :=
  even_numbers.toList = arr.toList.filter (fun x => x % 2 = 0)

theorem findEvenNumbers_spec_satisfied (arr: Array Nat) (h_precond : findEvenNumbers_precond (arr)) :
    findEvenNumbers_postcond (arr) (findEvenNumbers (arr) h_precond) h_precond := by
  simp [findEvenNumbers_postcond, findEvenNumbers]
-- </vc-theorems>
