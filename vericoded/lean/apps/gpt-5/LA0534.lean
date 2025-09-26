import Mathlib
-- <vc-preamble>
def ValidInput (A B C D : Int) : Prop :=
  1 ≤ A ∧ A ≤ 100 ∧ 1 ≤ B ∧ B ≤ 100 ∧ 1 ≤ C ∧ C ≤ 100 ∧ 1 ≤ D ∧ D ≤ 100

def TurnsToDefeat (health strength : Int) : Int :=
  (health + strength - 1) / strength

def TakahashiWins (A B C D : Int) : Bool :=
  let takahashi_turns := TurnsToDefeat C B
  let aoki_turns := TurnsToDefeat A D
  aoki_turns ≥ takahashi_turns

@[reducible, simp]
def solve_precond (A B C D : Int) : Prop :=
  ValidInput A B C D
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C D : Int) (h_precond : solve_precond A B C D) : String :=
  if TakahashiWins A B C D then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C D : Int) (result : String) (h_precond : solve_precond A B C D) : Prop :=
  result = (if TakahashiWins A B C D then "Yes" else "No") ∧ (result = "Yes" ∨ result = "No")

theorem solve_spec_satisfied (A B C D : Int) (h_precond : solve_precond A B C D) :
    solve_postcond A B C D (solve A B C D h_precond) h_precond := by
  cases h : TakahashiWins A B C D <;> simp [solve_postcond, solve, h]
-- </vc-theorems>
