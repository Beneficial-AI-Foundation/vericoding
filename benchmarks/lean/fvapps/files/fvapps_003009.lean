-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def circle_slash (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem circle_slash_range (n : Nat) (h : n > 0) :
  1 ≤ circle_slash n ∧ circle_slash n ≤ n :=
sorry

theorem circle_slash_odd_unless_power_of_two (n : Nat) (h : n > 0)
  (h_not_power_2 : ¬∃k, n = 2^k) :
  circle_slash n % 2 = 1 :=
sorry

theorem circle_slash_power_of_two (k : Nat) :
  circle_slash (2^k) = 1 :=
sorry

theorem circle_slash_binary_pattern (n : Nat) (h : n > 1) :

  circle_slash n = (n % (2^(Nat.log2 n))) * 2 + 1 :=
sorry

theorem circle_slash_one :
  circle_slash 1 = 1 :=
sorry
-- </vc-theorems>