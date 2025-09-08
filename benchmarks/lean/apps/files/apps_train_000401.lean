/-
Given a non-empty string s and a dictionary wordDict containing a list of non-empty words, determine if s can be segmented into a space-separated sequence of one or more dictionary words.

Note:

       The same word in the dictionary may be reused multiple times in the segmentation.
       You may assume the dictionary does not contain duplicate words.

Example 1:

Input: s = "leetcode", wordDict = ["leet", "code"]
Output: true
Explanation: Return true because "leetcode" can be segmented as "leet code".

Example 2:

Input: s = "applepenapple", wordDict = ["apple", "pen"]
Output: true
Explanation: Return true because "applepenapple" can be segmented as "apple pen apple".
             Note that you are allowed to reuse a dictionary word.

Example 3:

Input: s = "catsandog", wordDict = ["cats", "dog", "sand", "and", "cat"]
Output: false
-/

-- <vc-helpers>
-- </vc-helpers>

def word_break (s : String) (dict : List String) : Bool := sorry

def join_words (words : List String) : String := sorry

theorem word_break_valid_combination 
  (word_dict : List String) (h1 : word_dict.length > 0) :
  word_break (join_words (word_dict.take 5)) word_dict = true := sorry

theorem word_break_empty_string
  (s : String) (word_dict : List String) (h1 : word_dict.length > 0) :
  word_break "" word_dict = true := sorry

theorem word_break_empty_dict
  (s : String) (h1 : s.length > 0) :
  word_break s [] = false := sorry

theorem word_break_single_chars
  (word_dict : List String) (h1 : word_dict.length > 0) :
  let first_chars := word_dict.map (fun w => w.take 1)
  word_break (String.join first_chars) first_chars = true := sorry

theorem word_break_prefix_property
  (s : String) (word_dict : List String) (h1 : word_dict.length > 0) :
  word_break s word_dict = true →
  ∀ w ∈ word_dict, s.startsWith w → word_break w word_dict = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval word_break "leetcode" ["leet", "code"]

/-
info: True
-/
-- #guard_msgs in
-- #eval word_break "applepenapple" ["apple", "pen"]

/-
info: False
-/
-- #guard_msgs in
-- #eval word_break "catsandog" ["cats", "dog", "sand", "and", "cat"]

-- Apps difficulty: interview
-- Assurance level: unguarded