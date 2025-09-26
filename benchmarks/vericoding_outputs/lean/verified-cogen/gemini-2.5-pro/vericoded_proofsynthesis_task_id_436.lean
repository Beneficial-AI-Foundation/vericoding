import Mathlib
-- <vc-preamble>
@[reducible, simp]
def findNegativeNumbers_precond (arr : Array Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- A predicate that checks if an integer is negative. -/
@[simp]
def isNeg (x : Int) : Prop :=
  x < 0

-- LLM HELPER
/-- An instance to show that `isNeg` is a decidable predicate,
which is required for it to be used with `filter`. -/
instance : DecidablePred isNeg :=
  fun x => Int.decLt x 0

-- </vc-helpers>

-- <vc-definitions>
def findNegativeNumbers (arr : Array Int) (h_precond : findNegativeNumbers_precond arr) : Array Int :=
  arr.filter isNeg
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findNegativeNumbers_postcond (arr : Array Int) (negative_list: Array Int) (h_precond : findNegativeNumbers_precond arr) :=
  (negative_list.toList = (arr.toList.filter (fun x => x < 0)))

theorem findNegativeNumbers_spec_satisfied (arr: Array Int) (h_precond : findNegativeNumbers_precond arr) :
    findNegativeNumbers_postcond arr (findNegativeNumbers arr h_precond) h_precond := by
  simp [findNegativeNumbers, findNegativeNumbers_postcond, Array.toList_filter]
-- </vc-theorems>
