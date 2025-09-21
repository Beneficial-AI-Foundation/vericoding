-- <vc-preamble>
/- Precondition: All sub-arrays must be non-empty -/
@[reducible, simp]
def getFirstElements_precond (arr : Array (Array Int)) :=
  ∀ i, i < arr.size → arr[i]!.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getFirstElements (arr : Array (Array Int)) (h_precond : getFirstElements_precond arr) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def getFirstElements_postcond (arr : Array (Array Int)) (result : Array Int) (h_precond : getFirstElements_precond arr) :=
  arr.size = result.size ∧ (∀ i, i < arr.size → result[i]! = arr[i]![0]!)

theorem getFirstElements_spec_satisfied (arr : Array (Array Int)) (h_precond : getFirstElements_precond arr) :
    getFirstElements_postcond arr (getFirstElements arr h_precond) h_precond := by
  sorry
-- </vc-theorems>