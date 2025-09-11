-- <vc-preamble>
def sum_digits (n : Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_of_digits_string (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_digits_nonnegative (x : Int) :
  sum_digits x ≥ 0 :=
  sorry

theorem sum_digits_symmetric (x : Int) :
  sum_digits x = sum_digits (-x) :=
  sorry

theorem sum_digits_less_than_input (x : Int) (h : x.natAbs > 9) :
  sum_digits x < x.natAbs :=
  sorry

theorem sum_digits_single_digit (x : Int) 
  (h : 0 ≤ x.natAbs ∧ x.natAbs ≤ 9) :
  sum_digits x = x.natAbs :=
  sorry

theorem sum_digits_matches_string_sum (x : Int) :
  x ≥ 0 → sum_digits x = sum_of_digits_string x :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_digits 10

/-
info: 18
-/
-- #guard_msgs in
-- #eval sum_digits 99

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_digits -32
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded