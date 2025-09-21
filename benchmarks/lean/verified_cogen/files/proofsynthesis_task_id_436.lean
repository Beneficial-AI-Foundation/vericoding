-- <vc-preamble>
@[reducible, simp]
def findNegativeNumbers_precond (arr : Array Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findNegativeNumbers (arr : Array Int) (h_precond : findNegativeNumbers_precond arr) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findNegativeNumbers_postcond (arr : Array Int) (negative_list: Array Int) (h_precond : findNegativeNumbers_precond arr) :=
  (negative_list.toList = (arr.toList.filter (fun x => x < 0)))

theorem findNegativeNumbers_spec_satisfied (arr: Array Int) (h_precond : findNegativeNumbers_precond arr) :
    findNegativeNumbers_postcond arr (findNegativeNumbers arr h_precond) h_precond := by
  sorry
-- </vc-theorems>