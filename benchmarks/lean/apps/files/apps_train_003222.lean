-- <vc-preamble>
def narcissistic (n : Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digit_power_sum (n : Nat) : Nat :=
  sorry

-- For any natural number, narcissistic returns a boolean
-- </vc-definitions>

-- <vc-theorems>
theorem narcissistic_returns_bool (n : Nat) :
  ∃ (b : Bool), narcissistic n = b :=
  sorry 

-- The narcissistic function returns true when the sum of each digit raised to 
-- the power of number of digits equals the original number

theorem narcissistic_digit_power_sum (n : Nat) :
  narcissistic n = (n = digit_power_sum n) :=
  sorry

-- Known narcissistic numbers

theorem known_narcissistic_numbers :
  narcissistic 0 = true ∧ 
  narcissistic 1 = true ∧
  narcissistic 2 = true ∧
  narcissistic 3 = true ∧
  narcissistic 4 = true ∧
  narcissistic 5 = true ∧
  narcissistic 6 = true ∧
  narcissistic 7 = true ∧
  narcissistic 8 = true ∧
  narcissistic 9 = true ∧
  narcissistic 153 = true ∧
  narcissistic 370 = true ∧
  narcissistic 371 = true ∧
  narcissistic 407 = true :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval narcissistic 153

/-
info: True
-/
-- #guard_msgs in
-- #eval narcissistic 1634

/-
info: False
-/
-- #guard_msgs in
-- #eval narcissistic 123
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded