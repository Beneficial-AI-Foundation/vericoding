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
-- LLM HELPER
theorem Nat.mod_two_eq_zero_iff_not_one (n : Nat) : n % 2 = 0 ↔ ¬ (n % 2 = 1) := by
  constructor
  · intro h_zero h_one
    rw [h_zero] at h_one
    simp at h_one
  · intro h_not_one
    rcases Nat.mod_two_eq_zero_or_one n with h_zero | h_one
    · exact h_zero
    · contradiction
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
  dsimp [solve, solve_postcond]
  rw [Nat.mod_two_eq_zero_iff_not_one]
  split_ifs
  · simp [*]
  · simp [*]
-- </vc-theorems>
