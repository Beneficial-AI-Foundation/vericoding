-- <vc-preamble>
@[reducible, simp]
def isGreater_precond (arr : Array Int) (number : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isGreater (arr : Array Int) (number : Int) (h_precond : isGreater_precond arr number) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isGreater_postcond (arr : Array Int) (number : Int) (result: Bool) (h_precond : isGreater_precond arr number) :=
  (∀ i, i < arr.size → number > arr[i]!) ↔ result

theorem isGreater_spec_satisfied (arr: Array Int) (number: Int) (h_precond : isGreater_precond arr number) :
    isGreater_postcond arr number (isGreater arr number h_precond) h_precond := by
  sorry
-- </vc-theorems>