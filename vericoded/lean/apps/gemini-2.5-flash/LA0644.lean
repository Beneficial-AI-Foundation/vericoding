import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ 12 ∧ 1 ≤ b ∧ b ≤ 31

def TakahashiCount (a b : Int) : Int :=
  if a > b then a - 1 else a

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
def is_valid_month (m : Int) : Prop := 1 ≤ m ∧ m ≤ 12
def is_valid_day (d : Int) : Prop := 1 ≤ d ∧ d ≤ 31
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  if a > b then a - 1 else a
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int) (h_precond : solve_precond a b) : Prop :=
  result = TakahashiCount a b ∧ (a > b → result = a - 1) ∧ (a ≤ b → result = a)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  dsimp [solve, solve_postcond, TakahashiCount]
  split_ifs with h
  · simp [h]
  · simp [h, Int.not_lt.mp h]
-- </vc-theorems>
