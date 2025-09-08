/-
Given an input string (s) and a pattern (p), implement regular expression matching with support for '.' and '*'.

'.' Matches any single character.
'*' Matches zero or more of the preceding element.

The matching should cover the entire input string (not partial).

Note:

       s could be empty and contains only lowercase letters a-z.
       p could be empty and contains only lowercase letters a-z, and characters like . or *.

Example 1:

Input:
s = "aa"
p = "a"
Output: false
Explanation: "a" does not match the entire string "aa".

Example 2:

Input:
s = "aa"
p = "a*"
Output: true
Explanation: '*' means zero or more of the precedeng element, 'a'. Therefore, by repeating 'a' once, it becomes "aa".

Example 3:

Input:
s = "ab"
p = ".*"
Output: true
Explanation: ".*" means "zero or more (*) of any character (.)".

Example 4:

Input:
s = "aab"
p = "c*a*b"
Output: true
Explanation: c can be repeated 0 times, a can be repeated 1 time. Therefore it matches "aab".

Example 5:

Input:
s = "mississippi"
p = "mis*is*p*."
Output: false
-/

-- <vc-helpers>
-- </vc-helpers>

def isMatch (s : String) (p : String) : Bool := sorry 

@[simp]

theorem empty_pattern_matches_empty_string (s : String) : 
  isMatch s "" = !s.isEmpty = false := by sorry

@[simp]

theorem dot_star_matches_everything (s : String) : 
  isMatch s ".*" = true := by sorry 

@[simp]

theorem pattern_without_special_chars_exact_match (s p : String) 
  (h1 : ∀ c ∈ p.data, c ≠ '*' ∧ c ≠ '.') :
  isMatch s p = (s = p) := by sorry

@[simp]

theorem star_matches_zero_or_more (s : String) :
  isMatch s "a*" = (∀ c ∈ s.data, c = 'a') := by sorry

@[simp]

theorem self_matching (s : String) :
  isMatch s s = true := by sorry

@[simp]

theorem dots_match_same_length (s : String) :
  isMatch s (String.mk (List.replicate s.length '.')) = true := by sorry

@[simp]

theorem empty_string_cases_1 : isMatch "" "" = true := by sorry
@[simp]

theorem empty_string_cases_2 : isMatch "" "a*" = true := by sorry
@[simp] 

theorem empty_string_cases_3 : isMatch "a" "" = false := by sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_match "aa" "a"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_match "aa" "a*"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_match "ab" ".*"

-- Apps difficulty: interview
-- Assurance level: unguarded