-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def next_smaller (n : Nat) : Int :=
sorry

def has_same_digits (n m : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_smaller_result_positive (n : Nat) (h: n ≥ 10) :
  next_smaller n = -1 ∨ next_smaller n > 0 :=
sorry

theorem single_digit_returns_negative_one (n : Nat) (h: n < 10) :
  next_smaller n = -1 :=
sorry

theorem zero_returns_negative_one :
  next_smaller 0 = -1 :=
sorry

theorem result_preserves_number_of_digits (n : Nat) (h: n ≥ 10) :
  next_smaller n ≠ -1 →
  (String.length (toString (next_smaller n).natAbs) = String.length (toString n)) ∧
  next_smaller n < n :=
sorry
-- </vc-theorems>