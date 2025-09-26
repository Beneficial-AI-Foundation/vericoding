import Mathlib
-- <vc-preamble>
partial def countMaxMovesHelper (s : String) (i : Nat) (stack : List Char) (moves : Nat) : Nat :=
  if i ≥ s.length then moves
  else if stack.length > 0 ∧ s.data[i]! = stack.getLast! then
    countMaxMovesHelper s (i + 1) (stack.dropLast) (moves + 1)
  else
    countMaxMovesHelper s (i + 1) (stack ++ [s.data[i]!]) moves

def countMaxMoves (s : String) : Nat :=
  if s.length = 0 then 0
  else countMaxMovesHelper s 0 [] 0

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma to help with modular arithmetic
lemma nat_mod_two_cases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 :=
  Nat.mod_two_eq_zero_or_one n
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  if countMaxMoves s % 2 = 1 then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  (result = "Yes" ∨ result = "No") ∧
  (result = "Yes" ↔ countMaxMoves s % 2 = 1) ∧
  (result = "No" ↔ countMaxMoves s % 2 = 0)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  unfold solve solve_postcond
  split
  case isTrue h =>
    simp [h]
  case isFalse h =>
    simp [h]
    have : countMaxMoves s % 2 = 0 := by
      cases nat_mod_two_cases (countMaxMoves s) with
      | inl h₁ => exact h₁
      | inr h₂ => 
        rw [h₂] at h
        contradiction
    exact this
-- </vc-theorems>
