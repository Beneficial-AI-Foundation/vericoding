-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_palindrome_cuts (s : String) : Nat := sorry

def is_palindrome (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cuts_nonnegative (s : String) :
  min_palindrome_cuts s ≥ 0 := sorry

theorem binary_string_small_cuts (s : String) (h : s.length ≤ 2) :
  min_palindrome_cuts s ≤ 1 := sorry

theorem empty_string_no_cuts :
  min_palindrome_cuts "" = 0 := sorry

theorem single_char_no_cuts (c : Char) :
  min_palindrome_cuts (String.mk [c]) = 0 := sorry

theorem cuts_monotonicity :
  min_palindrome_cuts "a" ≤ min_palindrome_cuts "ab" ∧ 
  min_palindrome_cuts "ab" ≤ min_palindrome_cuts "abc" := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_palindrome_cuts "aab"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_palindrome_cuts "aba"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_palindrome_cuts "abba"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible