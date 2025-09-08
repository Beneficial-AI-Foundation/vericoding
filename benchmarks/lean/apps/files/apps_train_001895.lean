/-
You have a list of words and a pattern, and you want to know which words in words matches the pattern.
A word matches the pattern if there exists a permutation of letters p so that after replacing every letter x in the pattern with p(x), we get the desired word.
(Recall that a permutation of letters is a bijection from letters to letters: every letter maps to another letter, and no two letters map to the same letter.)
Return a list of the words in words that match the given pattern. 
You may return the answer in any order.

Example 1:
Input: words = ["abc","deq","mee","aqq","dkd","ccc"], pattern = "abb"
Output: ["mee","aqq"]
Explanation: "mee" matches the pattern because there is a permutation {a -> m, b -> e, ...}. 
"ccc" does not match the pattern because {a -> c, b -> c, ...} is not a permutation,
since a and b map to the same letter.

Note:

1 <= words.length <= 50
1 <= pattern.length = words[i].length <= 20
-/

-- <vc-helpers>
-- </vc-helpers>

def find_and_replace_pattern (words : List String) (pattern : String) : List String :=
  sorry

theorem word_length_matches_pattern (words : List String) (pattern : String) :
  ∀ w ∈ find_and_replace_pattern words pattern, String.length w = String.length pattern := by
  sorry

theorem result_subset_of_input (words : List String) (pattern : String) :
  ∀ w ∈ find_and_replace_pattern words pattern, w ∈ words := by
  sorry

theorem empty_input_returns_empty (pattern : String) :
  find_and_replace_pattern [] pattern = [] := by
  sorry

theorem identical_word_pattern_pair (pattern word : String) : 
  String.length word = String.length pattern →
  String.length (String.join (String.splitOn word "")) = 
  String.length (String.join (String.splitOn pattern "")) →
  word ∈ find_and_replace_pattern [word] word := by
  sorry

theorem pattern_mapping_consistency (pattern word : String) : 
  word ∈ find_and_replace_pattern [word] pattern →
  ∃ mapping : Char → Char,
  ∀ (i j : String.Pos), 
    (word.get i = word.get j ↔ pattern.get i = pattern.get j) := by
  sorry

/-
info: ['mee', 'aqq']
-/
-- #guard_msgs in
-- #eval find_and_replace_pattern ["abc", "deq", "mee", "aqq", "dkd", "ccc"] "abb"

/-
info: ['aa', 'bb']
-/
-- #guard_msgs in
-- #eval find_and_replace_pattern ["aa", "bb"] "cc"

/-
info: []
-/
-- #guard_msgs in
-- #eval find_and_replace_pattern ["ccc"] "abb"

-- Apps difficulty: interview
-- Assurance level: unguarded