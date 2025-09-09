/-
You are given a string s that consists of lower case English letters and brackets. 
Reverse the strings in each pair of matching parentheses, starting from the innermost one.
Your result should not contain any brackets.

Example 1:
Input: s = "(abcd)"
Output: "dcba"

Example 2:
Input: s = "(u(love)i)"
Output: "iloveu"
Explanation: The substring "love" is reversed first, then the whole string is reversed.

Example 3:
Input: s = "(ed(et(oc))el)"
Output: "leetcode"
Explanation: First, we reverse the substring "oc", then "etco", and finally, the whole string.

Example 4:
Input: s = "a(bcdefghijkl(mno)p)q"
Output: "apmnolkjihgfedcbq"

Constraints:

0 <= s.length <= 2000
s only contains lower case English characters and parentheses.
It's guaranteed that all parentheses are balanced.
-/

-- <vc-helpers>
-- </vc-helpers>

def reverse_parentheses (s : String) : String := sorry

theorem reverse_parentheses_length 
  (s : String) : 
  s.length = (reverse_parentheses s).length + s.data.count '(' + s.data.count ')' := 
  sorry

theorem reverse_parentheses_no_parens
  (s : String) :
  ¬ ((reverse_parentheses s).contains '(') ∧ ¬ ((reverse_parentheses s).contains ')') :=
  sorry

theorem reverse_parentheses_empty_parens :
  reverse_parentheses "()" = "" :=
  sorry

theorem reverse_parentheses_identity_no_parens
  (s : String) 
  (h : ¬ s.contains '(' ∧ ¬ s.contains ')') :
  reverse_parentheses s = s :=
  sorry

theorem reverse_parentheses_empty_string :
  reverse_parentheses "" = "" :=
  sorry

/-
info: 'dcba'
-/
-- #guard_msgs in
-- #eval reverse_parentheses "(abcd)"

/-
info: 'iloveu'
-/
-- #guard_msgs in
-- #eval reverse_parentheses "(u(love)i)"

/-
info: 'apmnolkjihgfedcbq'
-/
-- #guard_msgs in
-- #eval reverse_parentheses "a(bcdefghijkl(mno)p)q"

-- Apps difficulty: interview
-- Assurance level: unguarded