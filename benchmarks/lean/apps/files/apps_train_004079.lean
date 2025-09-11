-- <vc-preamble>
def sum_arrangements (n : Nat) : Nat := sorry

theorem deterministic (n : Nat) : 
  sum_arrangements n = sum_arrangements n := by sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digit_sum (n : Nat) : Nat := sorry

theorem multiple_of_digit_sum (n : Nat) (h : n > 0) :
  sum_arrangements n % digit_sum n = 0 := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit (n : Nat) (h : n > 0) (h₂ : n < 10) : 
  sum_arrangements n = n := by sorry

theorem positive_output (n : Nat) (h : n > 0) :
  sum_arrangements n > 0 := by sorry

/-
info: 187
-/
-- #guard_msgs in
-- #eval sum_arrangements 98

/-
info: 1332
-/
-- #guard_msgs in
-- #eval sum_arrangements 123

/-
info: 99990
-/
-- #guard_msgs in
-- #eval sum_arrangements 1185
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded