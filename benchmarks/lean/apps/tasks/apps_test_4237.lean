-- <vc-preamble>
def ValidInput (A B C D : Int) : Prop :=
  A ≥ 1 ∧ B ≥ A ∧ C ≥ 1 ∧ D ≥ 1

def NotDivisibleByEither (x C D : Int) : Prop :=
  x % C ≠ 0 ∧ x % D ≠ 0

def CountNotDivisible (A B C D : Int) : Int :=
  0

def f (n C D : Int) : Int :=
  0

@[reducible, simp]
def solve_precond (A B C D : Int) : Prop :=
  ValidInput A B C D
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C D : Int) (h_precond : solve_precond A B C D) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C D : Int) (result : Int) (h_precond : solve_precond A B C D) : Prop :=
  result ≥ 0 ∧ result = f B C D - f (A - 1) C D

theorem solve_spec_satisfied (A B C D : Int) (h_precond : solve_precond A B C D) :
    solve_postcond A B C D (solve A B C D h_precond) h_precond := by
  sorry
-- </vc-theorems>