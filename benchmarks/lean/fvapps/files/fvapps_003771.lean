-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def two_count (n : Nat) : Nat :=
sorry

def calc_divisions (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_count_non_negative (n : Nat) (h : n > 0) :
  two_count n ≥ 0 :=
sorry

theorem two_count_matches_divisions (n : Nat) (h : n > 0) :
  two_count n = calc_divisions n :=
sorry

theorem two_count_odd (n : Nat) (h₁ : n > 0) (h₂ : n % 2 = 1) :
  two_count n = 0 :=
sorry

theorem two_count_power_of_two (n : Nat) (h₁ : n > 0) (h₂ : n.isPowerOfTwo) :
  two_count n = Nat.log2 n :=
sorry

theorem two_count_multiplication (n k : Nat) (h : n > 0) :
  two_count (n * 2^k) = two_count n + k :=
sorry
-- </vc-theorems>