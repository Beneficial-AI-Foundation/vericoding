-- <vc-preamble>
def ValidInput (t w b : Int) : Prop :=
  t > 0 ∧ w > 0 ∧ b > 0

def ValidFraction (numerator denominator : Int) : Prop :=
  numerator ≥ 0 ∧ denominator > 0 ∧ numerator ≤ denominator

def IsIrreducibleFraction (numerator denominator : Int) (h_valid : ValidFraction numerator denominator) : Prop :=
  Int.gcd numerator denominator = 1

@[reducible, simp]
def solve_precond (t w b : Int) : Prop :=
  ValidInput t w b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (t w b : Int) (h_precond : solve_precond t w b) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (t w b : Int) (result : Int × Int) (h_precond : solve_precond t w b) : Prop :=
  ValidFraction result.1 result.2 ∧ IsIrreducibleFraction result.1 result.2 (by sorry)

theorem solve_spec_satisfied (t w b : Int) (h_precond : solve_precond t w b) :
    solve_postcond t w b (solve t w b h_precond) h_precond := by
  sorry
-- </vc-theorems>