-- <vc-preamble>
def ValidBrotherNumbers (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3 ∧ a ≠ b

def LateBrother (a b : Int) : Int :=
  6 - a - b

def IsValidResult (a b result : Int) : Prop :=
  ValidBrotherNumbers a b → (1 ≤ result ∧ result ≤ 3 ∧ result ≠ a ∧ result ≠ b)

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidBrotherNumbers a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  IsValidResult a b result ∧ result = LateBrother a b

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>