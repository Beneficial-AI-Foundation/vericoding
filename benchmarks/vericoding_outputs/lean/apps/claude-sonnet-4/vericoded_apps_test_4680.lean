import Mathlib
-- <vc-preamble>
def ValidInput (A B C : Int) : Prop :=
  1 ≤ A ∧ A ≤ 10 ∧ 1 ≤ B ∧ B ≤ 10 ∧ 1 ≤ C ∧ C ≤ 10

def CanFormHaiku (A B C : Int) : Prop :=
  (A = 5 ∧ B = 5 ∧ C = 7) ∨
  (A = 5 ∧ B = 7 ∧ C = 5) ∨
  (A = 7 ∧ B = 5 ∧ C = 5)

def ValidOutput (result : String) : Prop :=
  result = "YES" ∨ result = "NO"

@[reducible, simp]
def solve_precond (A B C : Int) : Prop :=
  ValidInput A B C
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Decidability instance for CanFormHaiku
instance (A B C : Int) : Decidable (CanFormHaiku A B C) := by
  unfold CanFormHaiku
  infer_instance
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C : Int) (h_precond : solve_precond A B C) : String :=
  if CanFormHaiku A B C then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C : Int) (result : String) (h_precond : solve_precond A B C) : Prop :=
  ValidOutput result ∧ (result = "YES" ↔ CanFormHaiku A B C)

theorem solve_spec_satisfied (A B C : Int) (h_precond : solve_precond A B C) :
    solve_postcond A B C (solve A B C h_precond) h_precond := by
  unfold solve_postcond ValidOutput solve
  constructor
  · -- ValidOutput: result is either "YES" or "NO"
    split <;> simp
  · -- Biconditional: result = "YES" ↔ CanFormHaiku A B C
    split
    case isTrue h => simp [h]
    case isFalse h => simp [h]
-- </vc-theorems>
