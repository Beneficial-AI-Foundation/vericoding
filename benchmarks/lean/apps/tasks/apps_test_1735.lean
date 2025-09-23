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
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  (result = "Yes" ∨ result = "No") ∧
  (result = "Yes" ↔ countMaxMoves s % 2 = 1) ∧
  (result = "No" ↔ countMaxMoves s % 2 = 0)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>