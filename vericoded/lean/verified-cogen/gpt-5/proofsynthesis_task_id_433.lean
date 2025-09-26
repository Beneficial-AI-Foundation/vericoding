import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isGreater_precond (arr : Array Int) (number : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem prop_iff_decide (p : Prop) [Decidable p] : (p ↔ decide p) := by
  by_cases hp : p
  · simp [hp]
  · simp [hp]
-- </vc-helpers>

-- <vc-definitions>
def isGreater (arr : Array Int) (number : Int) (h_precond : isGreater_precond arr number) : Bool :=
  decide (∀ i, i < arr.size → number > arr[i]!)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isGreater_postcond (arr : Array Int) (number : Int) (result: Bool) (h_precond : isGreater_precond arr number) :=
  (∀ i, i < arr.size → number > arr[i]!) ↔ result

theorem isGreater_spec_satisfied (arr: Array Int) (number: Int) (h_precond : isGreater_precond arr number) :
    isGreater_postcond arr number (isGreater arr number h_precond) h_precond := by
  simpa [isGreater_postcond, isGreater] using
    (prop_iff_decide (p := ∀ i, i < arr.size → number > arr[i]!))
-- </vc-theorems>

#check isGreater