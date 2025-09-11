-- <vc-preamble>
def digitSum (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isDivisibleByDigitSum (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isDivisibleByDigitSum_spec (n : Nat) (h : n > 0) :
  let ds := digitSum n
  isDivisibleByDigitSum n = "Yes" ↔ n % ds = 0
  := sorry

theorem isDivisibleByDigitSum_returns_valid_result (n : Nat) (h : n > 0) :
  isDivisibleByDigitSum n = "Yes" ∨ isDivisibleByDigitSum n = "No"
  := sorry

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval is_divisible_by_digit_sum 16

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval is_divisible_by_digit_sum 27

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval is_divisible_by_digit_sum 45
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded