/-
Consider the string s to be the infinite wraparound string of "abcdefghijklmnopqrstuvwxyz", so s will look like this: "...zabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcd....".

Now we have another string p. Your job is to find out how many unique non-empty substrings of p are present in s. In particular, your input is the string p and you need to output the number of different non-empty substrings of p in the string s.

Note: p consists of only lowercase English letters and the size of p might be over 10000.

Example 1:

Input: "a"
Output: 1

Explanation: Only the substring "a" of string "a" is in the string s.

Example 2:

Input: "cac"
Output: 2
Explanation: There are two substrings "a", "c" of string "cac" in the string s.

Example 3:

Input: "zab"
Output: 6
Explanation: There are six substrings "z", "a", "b", "za", "ab", "zab" of string "zab" in the string s.
-/

-- <vc-helpers>
-- </vc-helpers>

def find_substrings_in_wraparound (s: String) : Nat := sorry

theorem output_always_positive (s: String) : 
  find_substrings_in_wraparound s ≥ 0 := sorry

theorem single_char_min (s: String) :
  s.length ≥ 1 → find_substrings_in_wraparound s ≥ 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_substrings_in_wraparound "a"

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_substrings_in_wraparound "cac"

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_substrings_in_wraparound "zab"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible