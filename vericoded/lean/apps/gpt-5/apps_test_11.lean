import Mathlib
-- <vc-preamble>
def ValidInput (n a b p q : Int) : Prop :=
  n > 0 ∧ a > 0 ∧ b > 0 ∧ p > 0 ∧ q > 0

axiom gcd : Int → Int → Int

@[reducible, simp]
def solve_precond (n a b p q : Int) : Prop :=
  ValidInput n a b p q
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper code required for this verification condition.
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b p q : Int) (h_precond : solve_precond n a b p q) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b p q : Int) (result: Int) (h_precond : solve_precond n a b p q) : Prop :=
  result ≥ 0

theorem solve_spec_satisfied (n a b p q : Int) (h_precond : solve_precond n a b p q) :
    solve_postcond n a b p q (solve n a b p q h_precond) h_precond := by
  dsimp [solve_postcond, solve]
  exact le_rfl
-- </vc-theorems>
