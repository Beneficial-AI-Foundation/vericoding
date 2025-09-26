-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxLen : Nat :=
sorry

def sum_squares (n : Nat) : Nat :=
sorry

def square_pi (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_pi_monotone {n₁ n₂ : Nat} (h : n₁ ≤ n₂) (h2 : n₂ ≤ maxLen) :
  square_pi n₁ ≤ square_pi n₂ :=
sorry
-- </vc-theorems>