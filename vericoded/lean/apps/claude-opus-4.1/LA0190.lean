import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ b

def GcdOfRange (a b : Int) (h : ValidInput a b) : Int :=
  if a = b then a else 1

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple case
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  GcdOfRange a b h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  result = GcdOfRange a b h_precond ∧ 
  (a = b → result = a) ∧ 
  (a < b → result = 1)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve GcdOfRange
  simp only [solve_precond] at h_precond
  constructor
  · rfl
  constructor
  · intro h_eq
    simp [h_eq]
  · intro h_lt
    simp [ne_of_lt h_lt]
-- </vc-theorems>
