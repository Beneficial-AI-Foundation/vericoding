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
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C : Int) (h_precond : solve_precond A B C) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C : Int) (result : String) (h_precond : solve_precond A B C) : Prop :=
  ValidOutput result ∧ (result = "YES" ↔ CanFormHaiku A B C)

theorem solve_spec_satisfied (A B C : Int) (h_precond : solve_precond A B C) :
    solve_postcond A B C (solve A B C h_precond) h_precond := by
  sorry
-- </vc-theorems>