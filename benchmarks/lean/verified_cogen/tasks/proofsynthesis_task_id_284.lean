-- <vc-preamble>
@[reducible, simp]
def allElementsEquals_precond (arr : Array Int) (element : Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allElementsEquals (arr : Array Int) (element : Int) (h_precond : allElementsEquals_precond arr element) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def allElementsEquals_postcond (arr : Array Int) (element : Int) (result: Bool) (h_precond : allElementsEquals_precond arr element) :=
  (∀ i, i < arr.size → arr[i]! = element) ↔ result

theorem allElementsEquals_spec_satisfied (arr: Array Int) (element: Int) (h_precond : allElementsEquals_precond arr element) :
    allElementsEquals_postcond arr element (allElementsEquals arr element h_precond) h_precond := by
  sorry
-- </vc-theorems>