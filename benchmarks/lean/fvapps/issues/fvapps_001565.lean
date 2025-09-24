-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bernoulli_number (n : Nat) : Rat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_bernoulli_numbers_are_zero (n : Nat)
  (h : n ≥ 3)
  (h₂ : n % 2 = 1) :
  bernoulli_number n = 0 :=
sorry

theorem bernoulli_numbers_are_rational (n : Nat) :
  ∃ r : Rat, bernoulli_number n = r ∨ bernoulli_number n = 0 :=
sorry

theorem first_bernoulli_number :
  bernoulli_number 0 = 1 :=
sorry

theorem second_bernoulli_number :
  bernoulli_number 1 = -1/2 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval bernoulli_number 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval bernoulli_number 3

/-
info: Fraction(1, 42)
-/
-- #guard_msgs in
-- #eval bernoulli_number 6
-- </vc-theorems>