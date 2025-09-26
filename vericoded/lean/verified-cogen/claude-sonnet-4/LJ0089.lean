import Mathlib
-- <vc-preamble>
@[reducible, simp]
def findNegativeNumbers_precond (arr : Array Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- Use existing Mathlib Array.filter implementation
-- No additional helpers needed since Array.filter and related theorems exist in Mathlib
-- </vc-helpers>

-- <vc-definitions>
def findNegativeNumbers (arr : Array Int) (h_precond : findNegativeNumbers_precond arr) : Array Int :=
  arr.filter (fun x => x < 0)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findNegativeNumbers_postcond (arr : Array Int) (negative_list: Array Int) (h_precond : findNegativeNumbers_precond arr) :=
  (negative_list.toList = (arr.toList.filter (fun x => x < 0)))

theorem findNegativeNumbers_spec_satisfied (arr: Array Int) (h_precond : findNegativeNumbers_precond arr) :
    findNegativeNumbers_postcond arr (findNegativeNumbers arr h_precond) h_precond := by
  simp [findNegativeNumbers_postcond, findNegativeNumbers]
-- </vc-theorems>

def main : IO Unit := pure ()