import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 99

def ExpectedResult (n : Int) (h : ValidInput n) : String :=
  if n < 12 then
    if n = 1 ∨ n = 7 ∨ n = 9 ∨ n = 10 ∨ n = 11 then "NO" else "YES"
  else if 12 < n ∧ n < 30 then
    "NO"
  else if 69 < n ∧ n < 80 then
    "NO"
  else if 89 < n then
    "NO"
  else
    let lastDigit := n % 10
    if lastDigit ≠ 1 ∧ lastDigit ≠ 7 ∧ lastDigit ≠ 9 then "YES" else "NO"

def ValidOutput (result : String) : Prop :=
  result = "YES" ∨ result = "NO"

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : String :=
  if n < 12 then
    if n = 1 ∨ n = 7 ∨ n = 9 ∨ n = 10 ∨ n = 11 then "NO" else "YES"
  else if 12 < n ∧ n < 30 then
    "NO"
  else if 69 < n ∧ n < 80 then
    "NO"
  else if 89 < n then
    "NO"
  else
    let lastDigit := n % 10
    if lastDigit ≠ 1 ∧ lastDigit ≠ 7 ∧ lastDigit ≠ 9 then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : String) (h_precond : solve_precond n) : Prop :=
  ValidOutput result ∧ result = ExpectedResult n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
    -- Unfold the definitions of the postcondition, the function, and the expected result.
  unfold solve_postcond solve ExpectedResult

  -- The goal is now a conjunction. `And.intro` splits it into two subgoals.
  apply And.intro

  -- Goal 1: Prove the output is valid (i.e., "YES" or "NO").
  · -- Unfold the definition of a valid output.
    unfold ValidOutput
    -- `dsimp` simplifies the `let` binding for `lastDigit`.
    dsimp
    -- `split_ifs` performs case analysis on all conditional branches.
    split_ifs <;>
    -- For each case, the result is either "YES" or "NO", so `simp` can close the goal.
    simp

  -- Goal 2: Prove the function's output equals the expected result.
  · -- After unfolding, both sides of the equality are syntactically identical.
    -- `rfl` (reflexivity) proves this.
    rfl
-- </vc-theorems>
