/-
You are given a string S constisting of uppercase Latin letters. Is it possible to reorder the characters in this string to get a string with prefix "LTIME" and suffix "EMITL"?
We remind you that a prefix of a string is any substring which contains its first character, while a suffix of a string is substring containing its last character.

-----Input-----
The first line contains a single integer T, denoting the number of testcases. The descriptions of T test cases follow.
The first and only line of the test case description has one non-empty string S consisting of uppercase Latin letters only.

-----Output-----
For each testcase output a single line containing the string "YES" (without quotes) if it's possible to reorder the characters to get the required prefix and suffix, or "NO" (without quotes) otherwise.

-----Constraints-----
- Subtask 1 (23 points) : 1 ≤ T ≤ 100, 1 ≤ |S| ≤ 9
- Subtask 2 (77 points) : 1 ≤ T ≤ 1000, 1 ≤ |S| ≤ 100

-----Example-----
Input:3
LTIMEAZAZAITLME
LLLTTTIIIMMMEEEAHA
LTIMEM

Output:YES
YES
NO

-----Explanation-----
Test case 1: we can permute the last 5 letters and get LTIMEAZAZAEMITL
Test case 2: we have 3 copies of each of the letters 'L', 'T', 'I', 'M', 'E' so we can leave 5 of them in the beginning and move 5 of them to the end.
Test case 3: we have only one letter 'L' so we can't make necessary prefix and suffix at the same time.
-/

def isString : (s : String) → Bool := sorry
def canReorderString : (s : String) → String := sorry

-- <vc-helpers>
-- </vc-helpers>

def countChar (c : Char) (s : String) : Nat := sorry

def isValidLifetime (s : String) : Bool := sorry

theorem canReorderString_valid_output (s : String) :
  (canReorderString s = "YES") ∨ (canReorderString s = "NO") := sorry

theorem canReorderString_matches_validity (s : String) :
  canReorderString s = (if isValidLifetime s then "YES" else "NO") := sorry

theorem exactly_nine_chars (s : String) (h : s.length = 9) :
  countChar 'L' s ≥ 2 →
  countChar 'T' s ≥ 2 →
  countChar 'I' s ≥ 2 →
  countChar 'M' s ≥ 2 →
  countChar 'E' s ≥ 1 →
  canReorderString s = "YES" := sorry

theorem more_than_nine_chars (s : String) (h : s.length > 9) :
  countChar 'L' s ≥ 2 →
  countChar 'T' s ≥ 2 →
  countChar 'I' s ≥ 2 →
  countChar 'M' s ≥ 2 →
  countChar 'E' s ≥ 2 →
  canReorderString s = "YES" := sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_reorder_string "LTIMEAZAZAITLME"

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_reorder_string "LLLTTTIIIMMMEEEAHA"

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_reorder_string "LTIMEM"

-- Apps difficulty: interview
-- Assurance level: unguarded