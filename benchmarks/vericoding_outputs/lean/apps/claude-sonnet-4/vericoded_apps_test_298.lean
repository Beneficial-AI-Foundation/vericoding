import Mathlib
-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  k ≥ 1 ∧ n ≥ 1 ∧ k ≤ n

def TotalMoves (n k : Int) (h : ValidInput n k) : Int :=
  n / k

def FirstPlayerWins (n k : Int) (h : ValidInput n k) : Prop :=
  TotalMoves n k h % 2 = 1

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Decidability instance for integer modulo equality
instance decidableIntMod (a b : Int) : Decidable (a % b = 1) :=
  inferInstance

-- LLM HELPER: Decidability instance for FirstPlayerWins
instance decidableFirstPlayerWins (n k : Int) (h : ValidInput n k) : Decidable (FirstPlayerWins n k h) :=
  decidableIntMod (TotalMoves n k h) 2
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : String :=
  if FirstPlayerWins n k h_precond then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : String) (h_precond : solve_precond n k) : Prop :=
  (FirstPlayerWins n k h_precond → result = "YES") ∧
  (¬FirstPlayerWins n k h_precond → result = "NO")

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · intro h_wins
    simp [h_wins]
  · intro h_not_wins
    simp [h_not_wins]
-- </vc-theorems>
