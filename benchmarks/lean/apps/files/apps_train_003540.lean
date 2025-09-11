-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_zeros_n_double_fact (n : Int) : Nat := sorry

theorem count_zeros_non_negative (n : Int) : 
  count_zeros_n_double_fact n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_numbers_return_zero (n : Int) :
  n % 2 ≠ 0 → count_zeros_n_double_fact n = 0 := sorry

theorem larger_n_has_more_zeros (n : Int) :
  n % 2 = 0 → n ≥ 10 → 
  count_zeros_n_double_fact (2 * n) ≥ count_zeros_n_double_fact n := sorry

theorem small_numbers_have_zero_count (n : Int) :
  n ≤ 8 → count_zeros_n_double_fact n = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_zeros_n_double_fact 8

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_zeros_n_double_fact 30

/-
info: 62
-/
-- #guard_msgs in
-- #eval count_zeros_n_double_fact 500
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded