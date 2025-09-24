-- <vc-preamble>
@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)

theorem lastDigit_spec_satisfied (n: Nat) (h_precond : lastDigit_precond (n)) :
    lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>