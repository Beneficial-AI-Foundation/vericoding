-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_palindrome (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_palindrome_range (n : Nat) (h : 1 ≤ n ∧ n ≤ 8) : 
  0 ≤ largest_palindrome n ∧ largest_palindrome n ≤ 1337 :=
sorry

theorem largest_palindrome_invalid (n : Nat) (h : n ≥ 9) :
  largest_palindrome n = 0 :=
sorry

theorem largest_palindrome_deterministic (n : Nat) :
  largest_palindrome n = largest_palindrome n :=
sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval largest_palindrome 1

/-
info: 987
-/
-- #guard_msgs in
-- #eval largest_palindrome 2

/-
info: 123
-/
-- #guard_msgs in
-- #eval largest_palindrome 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible