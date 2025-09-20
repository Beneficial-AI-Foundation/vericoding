-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def word_count (text : String) : Nat := sorry

def OMIT : List String := ["a", "the", "on", "at", "of", "upon", "in", "as"]
-- </vc-definitions>

-- <vc-theorems>
theorem word_count_with_valid_words (text : String) (words : List String) 
  (h1 : ∀ w ∈ words, ∀ c ∈ w.data, 'a' ≤ c ∧ c ≤ 'z')
  (h2 : text = String.join (List.intersperse " " words))
  (h3 : words ≠ []) :
  word_count text = (words.filter (fun w => !OMIT.contains w)).length := sorry

theorem omitted_words_count_zero (text : String) (words : List String)
  (h1 : ∀ w ∈ words, OMIT.contains w)  
  (h2 : words ≠ [])
  (h3 : text = String.join (List.intersperse " " words)) :
  word_count text = 0 := sorry

theorem word_count_empty : word_count "" = 0 := sorry

theorem word_count_spaces : word_count "   " = 0 := sorry 

theorem word_count_special_chars : word_count "!@#$%^&*()" = 0 := sorry
-- </vc-theorems>