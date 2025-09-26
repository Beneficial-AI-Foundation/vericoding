import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3

def IsOdd (n : Int) : Prop :=
  n % 2 = 1

def ExistsOddProduct (a b : Int) (h : ValidInput a b) : Prop :=
  ∃ c, 1 ≤ c ∧ c ≤ 3 ∧ IsOdd (a * b * c)

def ShouldAnswerYes (a b : Int) (h : ValidInput a b) : Bool :=
  a ≠ 2 ∧ b ≠ 2

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem if_same_String (c : Bool) :
  (if c then "Yes" else "No") = (if c then "Yes" else "No") := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : String :=
  if ShouldAnswerYes a b h_precond then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : String) (h_precond : solve_precond a b) : Prop :=
  result = (if ShouldAnswerYes a b h_precond then "Yes" else "No")

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  simp [solve, solve_postcond]
-- </vc-theorems>
