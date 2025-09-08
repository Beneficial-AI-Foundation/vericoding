/-
Given a string that consists of only uppercase English letters, you can replace any letter in the string with another letter at most k times. Find the length of a longest substring containing all repeating letters you can get after performing the above operations.

Note:
Both the string's length and k will not exceed 104.

Example 1:

Input:
s = "ABAB", k = 2

Output:
4

Explanation:
Replace the two 'A's with two 'B's or vice versa.

Example 2:

Input:
s = "AABABBA", k = 1

Output:
4

Explanation:
Replace the one 'A' in the middle with 'B' and form "AABBBBA".
The substring "BBBB" has the longest repeating letters, which is 4.
-/

-- <vc-helpers>
-- </vc-helpers>

def character_replacement (s : String) (k : Nat) : Nat :=
  sorry

theorem character_replacement_basic_properties
  (s : String) (k : Nat) :
  let result := character_replacement s k
  -- Result bounded by string length
  result ≤ s.length ∧
  -- For non-empty strings, result at least min(len(s), k+1)
  (s ≠ "" → result ≥ min s.length (k+1)) ∧
  -- Empty string returns 0
  (s = "" → result = 0) ∧
  -- If k ≥ length, result equals length
  (k ≥ s.length → result = s.length) :=
  sorry

theorem character_replacement_empty
  (k : Nat) :
  character_replacement "" k = 0 :=
  sorry

theorem character_replacement_monotonic
  (s : String) (k : Nat) :
  s ≠ "" →
  character_replacement s k ≤ character_replacement s (k + 1) :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval character_replacement "ABAB" 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval character_replacement "AABABBA" 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval character_replacement "" 2

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible