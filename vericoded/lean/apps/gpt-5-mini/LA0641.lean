import Mathlib
-- <vc-preamble>
def ValidInput (A B C D : Int) : Prop :=
  1 ≤ A ∧ A ≤ 1000 ∧ 1 ≤ B ∧ B ≤ 1000 ∧ 1 ≤ C ∧ C ≤ 1000 ∧ 1 ≤ D ∧ D ≤ 1000

def MinTotalFare (A B C D : Int) : Int :=
  (if A < B then A else B) + (if C < D then C else D)

@[reducible, simp]
def solve_precond (A B C D : Int) : Prop :=
  ValidInput A B C D
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- A small helper returning the minimum of two Ints. -/
def myMin (x y : Int) : Int := if x < y then x else y

@[simp] theorem myMin_def (x y : Int) : myMin x y = (if x < y then x else y) := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C D : Int) (h_precond : solve_precond A B C D) : Int :=
  myMin A B + myMin C D
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C D : Int) (result: Int) (h_precond : solve_precond A B C D) : Prop :=
  result = MinTotalFare A B C D

theorem solve_spec_satisfied (A B C D : Int) (h_precond : solve_precond A B C D) :
    solve_postcond A B C D (solve A B C D h_precond) h_precond := by
  simp [solve, MinTotalFare]
-- </vc-theorems>
