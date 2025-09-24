-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_beautiful_numbers (n : Nat) : Nat := sorry

theorem count_beautiful_range (n : Nat) (h : n > 0) :
  1 ≤ count_beautiful_numbers n ∧ count_beautiful_numbers n ≤ 81 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_beautiful_monotonic (n : Nat) (h : n > 1) :
  count_beautiful_numbers n ≥ count_beautiful_numbers (n-1) := sorry

theorem count_beautiful_single_digits (d : Nat) (h1 : d > 0) (h2 : d ≤ 9) :
  count_beautiful_numbers d = d := sorry

theorem count_beautiful_powers_ten :
  count_beautiful_numbers 99 = 18 ∧ 
  count_beautiful_numbers 999 = 27 ∧
  count_beautiful_numbers 9999 = 36 := sorry
-- </vc-theorems>