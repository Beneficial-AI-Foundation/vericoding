/-
You are given an array of strings words and a string chars.
A string is good if it can be formed by characters from chars (each character can only be used once).
Return the sum of lengths of all good strings in words.

Example 1:
Input: words = ["cat","bt","hat","tree"], chars = "atach"
Output: 6
Explanation: 
The strings that can be formed are "cat" and "hat" so the answer is 3 + 3 = 6.

Example 2:
Input: words = ["hello","world","leetcode"], chars = "welldonehoneyr"
Output: 10
Explanation: 
The strings that can be formed are "hello" and "world" so the answer is 5 + 5 = 10.

Note:

1 <= words.length <= 1000
1 <= words[i].length, chars.length <= 100
All strings contain lowercase English letters only.
-/

def String.count (s : String) (c : Char) : Nat := sorry

def countCharacters : List String → String → Nat
  | words, chars => sorry

-- <vc-helpers>
-- </vc-helpers>

def canForm (w : String) (chars : String) : Bool :=
  let check (c : Char) := w.count c ≤ chars.count c
  w.data.all check

theorem count_characters_nonnegative (words : List String) (chars : String) :
  countCharacters words chars ≥ 0 := by sorry

theorem count_characters_bounded_by_total_length (words : List String) (chars : String) :
  countCharacters words chars ≤ (words.map String.length).foldl (· + ·) 0 := by sorry

theorem count_characters_empty_chars (words : List String) :
  countCharacters words "" = 0 := by sorry

theorem count_characters_monotone (words : List String) (chars s : String) :
  countCharacters words (chars ++ s) ≥ countCharacters words chars := by sorry

theorem count_characters_substring_property (words : List String) (chars : String) :
  countCharacters words chars = 
    (List.map String.length 
      (List.filter (fun w => canForm w chars) words)).foldl (· + ·) 0 := by sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval countCharacters ["cat", "bt", "hat", "tree"] "atach"

/-
info: 10
-/
-- #guard_msgs in
-- #eval countCharacters ["hello", "world", "leetcode"] "welldonehoneyr"

/-
info: 8
-/
-- #guard_msgs in
-- #eval countCharacters ["good", "best", "word"] "bestword"

-- Apps difficulty: introductory
-- Assurance level: guarded