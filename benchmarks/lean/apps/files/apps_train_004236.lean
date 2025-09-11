-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_narcissistic : Nat → Bool := sorry

def poweredDigitsSum : Nat → Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_narcissistic {n : Nat} (h : n < 10) : 
  is_narcissistic n = true := sorry

theorem narcissistic_sum_property {n : Nat} (h : is_narcissistic n = true) :
  poweredDigitsSum n = n := sorry

theorem non_narcissistic_sum_property {n : Nat} (h : is_narcissistic n = false) :
  poweredDigitsSum n ≠ n := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_narcissistic 153

/-
info: True
-/
-- #guard_msgs in
-- #eval is_narcissistic 370

/-
info: True
-/
-- #guard_msgs in
-- #eval is_narcissistic 407
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded