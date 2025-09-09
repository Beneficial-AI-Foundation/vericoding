def replace_words (dict : List String) (sentence : String) : String := sorry

def splitIntoWords (s : String) : List String := s.split (· == ' ')

-- <vc-helpers>
-- </vc-helpers>

def wordCount (s : String) : Nat := (splitIntoWords s).length

theorem replace_words_output_length_matches_input
  (dict : List String) (words : List String) (h_words : words.length > 0) 
  (sentence := String.intercalate " " words) : 
  wordCount (replace_words dict sentence) = words.length := sorry

theorem replace_words_output_words_valid
  (dict : List String) (words : List String) (h_words : words.length > 0)
  (sentence := String.intercalate " " words) :
  let result := splitIntoWords (replace_words dict sentence)
  ∀ (i : Nat) (h : i < words.length),
    result[i]! = words[i]! ∨ result[i]! ∈ dict := sorry

theorem replace_words_replacement_preserves_prefix
  (dict : List String) (words : List String) (h_words : words.length > 0)
  (sentence := String.intercalate " " words) :
  let result := splitIntoWords (replace_words dict sentence)
  ∀ (i : Nat) (h : i < words.length),
    result[i]! ∈ dict → words[i]!.startsWith result[i]! := sorry

theorem empty_dict_preserves_input
  (dict : List String) (word : String) (h_dict : dict = []) :
  replace_words dict word = word := sorry

theorem replace_words_idempotent
  (dict : List String) (words : List String) (h_words : words.length > 0) 
  (h_dict : dict.length > 0)
  (sentence := String.intercalate " " words) :
  let once := replace_words dict sentence
  let twice := replace_words dict once
  once = twice := sorry

/-
info: 'the cat was rat by the bat'
-/
-- #guard_msgs in
-- #eval replace_words ["cat", "bat", "rat"] "the cattle was rattled by the battery"

/-
info: 'a a a'
-/
-- #guard_msgs in
-- #eval replace_words ["a", "aa", "aaa"] "aa aaa aaaa"

-- Apps difficulty: interview
-- Assurance level: unguarded