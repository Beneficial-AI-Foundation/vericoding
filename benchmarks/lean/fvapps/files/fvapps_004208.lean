-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countDivisors (n : Nat) : Nat :=
  sorry

def divNum (a b : Nat) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divNum_invalid_range {a b : Nat} (h : a > b) :
  divNum a b = none :=
sorry

theorem divNum_result_in_range {a b : Nat} (h : a ≤ b) (result : Nat) :
  divNum a b = some result → a ≤ result ∧ result ≤ b :=
sorry

theorem divNum_max_divisors {a b result : Nat} (h : a ≤ b) :
  divNum a b = some result →
  ∀ x, a ≤ x ∧ x ≤ b → countDivisors x ≤ countDivisors result :=
sorry

theorem divNum_equal_inputs (x : Nat) :
  divNum x x = some x :=
sorry
-- </vc-theorems>