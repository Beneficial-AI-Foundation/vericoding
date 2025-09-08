/-
Given a string s containing only lower case English letters and the '?' character, convert all the '?' characters into lower case letters such that the final string does not contain any consecutive repeating characters. You cannot modify the non '?' characters.
It is guaranteed that there are no consecutive repeating characters in the given string except for '?'.
Return the final string after all the conversions (possibly zero) have been made. If there is more than one solution, return any of them. It can be shown that an answer is always possible with the given constraints.

Example 1:
Input: s = "?zs"
Output: "azs"
Explanation: There are 25 solutions for this problem. From "azs" to "yzs", all are valid. Only "z" is an invalid modification as the string will consist of consecutive repeating characters in "zzs".
Example 2:
Input: s = "ubv?w"
Output: "ubvaw"
Explanation: There are 24 solutions for this problem. Only "v" and "w" are invalid modifications as the strings will consist of consecutive repeating characters in "ubvvw" and "ubvww".

Example 3:
Input: s = "j?qg??b"
Output: "jaqgacb"

Example 4:
Input: s = "??yw?ipkj?"
Output: "acywaipkja"

Constraints:

1 <= s.length <= 100
s contains only lower case English letters and '?'.
-/

-- <vc-helpers>
-- </vc-helpers>

def modify_string (s : String) : String :=
  sorry

theorem modify_string_empty : 
  modify_string "" = "" := sorry 

theorem modify_string_no_question_marks {s : String} 
  (h : ∀ c ∈ s.data, 'a' ≤ c ∧ c ≤ 'z') :
  modify_string s = s := sorry

theorem modify_string_length {s : String} :
  (modify_string s).length = s.length := sorry

theorem modify_string_lowercase {s : String} :
  ∀ c ∈ (modify_string s).data, 'a' ≤ c ∧ c ≤ 'z' := sorry

theorem modify_string_no_adjacent_same {s : String} :
  ∀ i, i + 1 < (modify_string s).length → 
    (modify_string s).data[i]! ≠ (modify_string s).data[i+1]! := sorry

theorem modify_string_preserves_non_question {s : String} {i : Nat} :
  i < s.length →
  s.data[i]! ≠ '?' → 
  (modify_string s).data[i]! = s.data[i]! := sorry

/-
info: 'azs'
-/
-- #guard_msgs in
-- #eval modify_string "?zs"

/-
info: len('j?qg??b')
-/
-- #guard_msgs in
-- #eval len modify_string("j?qg??b")

-- Apps difficulty: introductory
-- Assurance level: unguarded