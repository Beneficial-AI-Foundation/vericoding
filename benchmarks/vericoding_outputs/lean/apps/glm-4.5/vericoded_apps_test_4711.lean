import Mathlib
-- <vc-preamble>
def ValidInput (a b c : Int) : Prop :=
  1 ≤ a ∧ a ≤ 10000 ∧ 1 ≤ b ∧ b ≤ 10000 ∧ 1 ≤ c ∧ c ≤ 10000

def MinOfThree (x y z : Int) : Int :=
  if x ≤ y ∧ x ≤ z then x
  else if y ≤ z then y
  else z

def CorrectResult (a b c : Int) : Int :=
  MinOfThree (a + b) (a + c) (b + c)

@[reducible, simp]
def solve_precond (a b c : Int) : Prop :=
  ValidInput a b c
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemma for MinOfThree properties
lemma MinOfThree_correct (x y z : Int) :
  MinOfThree x y z = if x ≤ y ∧ x ≤ z then x else if y ≤ z then y else z := by
  rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c : Int) (h_precond : solve_precond a b c) : Int :=
  MinOfThree (a + b) (a + c) (b + c)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c : Int) (result : Int) (h_precond : solve_precond a b c) : Prop :=
  result = CorrectResult a b c

theorem solve_spec_satisfied (a b c : Int) (h_precond : solve_precond a b c) :
    solve_postcond a b c (solve a b c h_precond) h_precond := by
  unfold solve solve_postcond CorrectResult
  rfl
-- </vc-theorems>
