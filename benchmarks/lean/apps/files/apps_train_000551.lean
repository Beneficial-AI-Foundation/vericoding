-- <vc-helpers>
-- </vc-helpers>

def check_palindrome_possible (s1 s2 : String) : String := sorry

theorem check_palindrome_possible_symmetric 
  (s1 s2 : String) :
  check_palindrome_possible s1 s2 = check_palindrome_possible s2 s1 := 
sorry

theorem check_palindrome_possible_self
  (s : String) :
  s ≠ "" → check_palindrome_possible s s = "Yes" := 
sorry

theorem check_palindrome_possible_output_valid
  (s1 s2 : String) : 
  check_palindrome_possible s1 s2 = "Yes" ∨ check_palindrome_possible s1 s2 = "No" :=
sorry

theorem check_palindrome_possible_common_char
  (s1 s2 : String) :
  s1 ≠ "" →
  s2 ≠ "" →
  (∃ c, c ∈ s1.data ∧ c ∈ s2.data) →
  check_palindrome_possible s1 s2 = "Yes" :=
sorry

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval check_palindrome_possible "abc" "abc"

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval check_palindrome_possible "a" "b"

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval check_palindrome_possible "abba" "baab"

-- Apps difficulty: interview
-- Assurance level: unguarded