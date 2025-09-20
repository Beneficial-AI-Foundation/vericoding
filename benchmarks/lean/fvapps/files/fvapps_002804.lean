-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.reverse (s : String) : String :=
sorry

def split (s : String) (sep : String) : List String :=
sorry

def reverse_sentence (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_count_preserved (words : List String) :
  let sentence := " ".intercalate words
  let reversed := reverse_sentence sentence
  (split sentence " ").length = (split reversed " ").length :=
sorry

theorem empty_string :
  reverse_sentence "" = "" :=
sorry

theorem each_word_reversed (s : String) :
  let original_words := split s " "
  let result_words := split (reverse_sentence s) " "
  ∀ i, i < original_words.length →
    result_words[i]! = String.reverse original_words[i]! :=
sorry
-- </vc-theorems>