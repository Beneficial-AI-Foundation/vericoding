-- <vc-preamble>
def splitIntoWords (s : String) : List String := s.split (· == ' ')

def wordCount (s : String) : Nat := (splitIntoWords s).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace_words (dict : List String) (sentence : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem replace_words_output_length_matches_input
  (dict : List String) (words : List String) (h_words : words.length > 0)
  (sentence := String.intercalate " " words) :
  wordCount (replace_words dict sentence) = words.length :=
sorry

theorem replace_words_output_words_valid
  (dict : List String) (words : List String) (h_words : words.length > 0)
  (sentence := String.intercalate " " words) :
  let result := splitIntoWords (replace_words dict sentence)
  ∀ (i : Nat) (h : i < words.length),
    result[i]! = words[i]! ∨ result[i]! ∈ dict :=
sorry

theorem replace_words_replacement_preserves_prefix
  (dict : List String) (words : List String) (h_words : words.length > 0)
  (sentence := String.intercalate " " words) :
  let result := splitIntoWords (replace_words dict sentence)
  ∀ (i : Nat) (h : i < words.length),
    result[i]! ∈ dict → words[i]!.startsWith result[i]! :=
sorry

theorem empty_dict_preserves_input
  (dict : List String) (word : String) (h_dict : dict = []) :
  replace_words dict word = word :=
sorry

theorem replace_words_idempotent
  (dict : List String) (words : List String) (h_words : words.length > 0)
  (h_dict : dict.length > 0)
  (sentence := String.intercalate " " words) :
  let once := replace_words dict sentence
  let twice := replace_words dict once
  once = twice :=
sorry
-- </vc-theorems>