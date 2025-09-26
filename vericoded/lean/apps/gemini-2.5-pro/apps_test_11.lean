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
/-- Square of an integer. -/
def isq (x : Int) : Int := x * x

-- LLM HELPER
/-- The square of an integer is non-negative. -/
theorem isq_nonneg (x : Int) : isq x ≥ 0 := by
  unfold isq
  exact mul_self_nonneg x
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b p q : Int) (h_precond : solve_precond n a b p q) : Int :=
  n + isq (Int.gcd a p) + isq (Int.gcd b q)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b p q : Int) (result: Int) (h_precond : solve_precond n a b p q) : Prop :=
  result ≥ 0

theorem solve_spec_satisfied (n a b p q : Int) (h_precond : solve_precond n a b p q) :
    solve_postcond n a b p q (solve n a b p q h_precond) h_precond := by
  dsimp [solve_postcond, solve]
  apply Int.add_nonneg
  · apply Int.add_nonneg
    · dsimp [solve_precond, ValidInput] at h_precond
      linarith [h_precond.1]
    · exact isq_nonneg (Int.gcd a p)
  · exact isq_nonneg (Int.gcd b q)
-- </vc-theorems>
