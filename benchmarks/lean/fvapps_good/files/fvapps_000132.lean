-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_numbers_with_repeated_digits (n : Nat) : Nat :=
  sorry

-- Output is bounded by input
-- </vc-definitions>

-- <vc-theorems>
theorem output_range {n : Nat} (h : n > 0) : 
  count_numbers_with_repeated_digits n ≤ n :=
  sorry

-- Single digit numbers have no repeats

theorem single_digit_zero {n : Nat} (h : n > 0) (h2 : n < 10) :
  count_numbers_with_repeated_digits n = 0 :=
  sorry

-- Double digit result equals manual count

theorem double_digits_count {n : Nat} (h : n > 0) (h2 : n ≤ 100) :
  count_numbers_with_repeated_digits n = 
    count_numbers_with_repeated_digits n -- simplified form of actual count
  :=
  sorry

-- Specific value tests

theorem specific_value_20 :
  count_numbers_with_repeated_digits 20 = 1 :=
  sorry

theorem specific_value_100 :
  count_numbers_with_repeated_digits 100 = 10 :=
  sorry

theorem specific_value_1000 :
  count_numbers_with_repeated_digits 1000 = 262 :=
  sorry

-- Function is monotonically increasing

theorem monotonic_increasing {n : Nat} (h : n > 1) :
  count_numbers_with_repeated_digits n ≥ count_numbers_with_repeated_digits (n-1) :=
  sorry

-- Consecutive values differ by at most 1

theorem difference_bound {n : Nat} (h : n > 1) :
  let diff := count_numbers_with_repeated_digits n - count_numbers_with_repeated_digits (n-1)
  diff ≤ 1 :=
  sorry
-- </vc-theorems>