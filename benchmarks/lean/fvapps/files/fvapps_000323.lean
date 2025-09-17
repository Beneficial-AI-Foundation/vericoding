-- <vc-preamble>
def count_palindromic_substrings (s: String) : Nat :=
  sorry

def is_palindrome (s : String) : Bool :=
  sorry

def string_reverse (s : String) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_repeat (c : Char) (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimum_palindromes (s : String) (h : s.length > 0) : 
  count_palindromic_substrings s ≥ s.length :=
sorry 

theorem empty_string :
  count_palindromic_substrings "" = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_palindromic_substrings "abc"

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_palindromic_substrings "aaa"

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_palindromic_substrings "racecar"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible