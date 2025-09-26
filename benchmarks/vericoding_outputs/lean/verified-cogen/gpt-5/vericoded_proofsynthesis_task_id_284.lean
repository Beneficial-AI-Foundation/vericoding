import Mathlib
-- <vc-preamble>
@[reducible, simp]
def allElementsEquals_precond (arr : Array Int) (element : Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem vc_prop_iff_decide (p : Prop) [Decidable p] : p ↔ decide p := by
  by_cases h : p <;> simp [h]
-- </vc-helpers>

-- <vc-definitions>
def allElementsEquals (arr : Array Int) (element : Int) (h_precond : allElementsEquals_precond arr element) : Bool :=
  decide (∀ i, i < arr.size → arr[i]! = element)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def allElementsEquals_postcond (arr : Array Int) (element : Int) (result: Bool) (h_precond : allElementsEquals_precond arr element) :=
  (∀ i, i < arr.size → arr[i]! = element) ↔ result

theorem allElementsEquals_spec_satisfied (arr: Array Int) (element: Int) (h_precond : allElementsEquals_precond arr element) :
    allElementsEquals_postcond arr element (allElementsEquals arr element h_precond) h_precond := by
  classical
  dsimp [allElementsEquals_postcond, allElementsEquals]
  exact (vc_prop_iff_decide (p := ∀ i, i < arr.size → arr[i]! = element))
-- </vc-theorems>
