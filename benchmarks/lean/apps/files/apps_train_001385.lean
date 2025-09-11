-- <vc-preamble>
def find_min_troops_to_ruin (s: String) : Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPalindrome (s: String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_troops_bounds (s: String) :
  let result := find_min_troops_to_ruin s
  0 ≤ result ∧ result ≤ 2 :=
sorry

theorem empty_string_troops (s: String) :
  s = "" → find_min_troops_to_ruin s = 0 :=
sorry

theorem palindrome_troops (s: String) :
  s ≠ "" ∧ isPalindrome s → find_min_troops_to_ruin s = 1 :=
sorry

theorem non_palindrome_troops (s: String) :
  s ≠ "" ∧ ¬isPalindrome s → find_min_troops_to_ruin s = 2 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_troops_to_ruin "abbabaab"

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_troops_to_ruin "abba"

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_troops_to_ruin "ab"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible