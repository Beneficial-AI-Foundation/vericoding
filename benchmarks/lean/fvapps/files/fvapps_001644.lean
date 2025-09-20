-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cut_log (prices : List Nat) (n : Nat) : Nat := sorry

theorem cut_log_non_negative (prices : List Nat) (n : Nat) :
  cut_log prices n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cut_log_monotonic (prices : List Nat) (n : Nat) :
  n > 0 → cut_log prices n ≥ cut_log prices (n-1) := sorry

theorem cut_log_zero (prices : List Nat) :
  cut_log prices 0 = 0 := sorry

theorem cut_log_single_unit (prices : List Nat) :
  prices ≠ [] → prices.length > 1 → cut_log prices 1 = prices[1]! := sorry
-- </vc-theorems>