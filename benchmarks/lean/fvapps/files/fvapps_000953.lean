-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_special_numbers (n: Nat) : Nat := sorry

theorem under_100_returns_self {n: Nat} (h: n ≥ 1 ∧ n ≤ 99) : 
  count_special_numbers n = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem three_digit_bounds {n: Nat} (h: n ≥ 100 ∧ n ≤ 999) :
  99 ≤ count_special_numbers n ∧ count_special_numbers n ≤ n := sorry

theorem four_digit_bounds {n: Nat} (h: n ≥ 1000 ∧ n ≤ 9999) :
  189 ≤ count_special_numbers n ∧ count_special_numbers n ≤ n := sorry

theorem output_monotonic {n m: Nat} (h: n ≤ m) :
  count_special_numbers n ≤ count_special_numbers m := sorry

theorem basic_properties {n: Nat} (h: n ≥ 1 ∧ n ≤ 9999) :
  count_special_numbers n ≥ 0 ∧ count_special_numbers n ≤ n := sorry
-- </vc-theorems>