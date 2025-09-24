-- <vc-preamble>
def ValidInput (a b c d : Int) : Prop :=
  1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100 ∧ 1 ≤ d ∧ d ≤ 100

def CanCommunicate (a b c d : Int) : Prop :=
  Int.natAbs (a - c) ≤ d ∨ (Int.natAbs (a - b) ≤ d ∧ Int.natAbs (b - c) ≤ d)

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  ValidInput a b c d
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result : String) (h_precond : solve_precond a b c d) : Prop :=
  (result = "Yes" ↔ CanCommunicate a b c d) ∧ (result = "Yes" ∨ result = "No")

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  sorry
-- </vc-theorems>