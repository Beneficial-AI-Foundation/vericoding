-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrange_words (s : String) : String := sorry

theorem arrange_words_length_order (text : String) (h : text ≠ "") :
  let result := arrange_words text
  let result_words := (result.toLower.split (· = ' '))
  ∀ i, i < result_words.length - 1 →
    result_words[i]!.length ≤ result_words[i+1]!.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arrange_words_preserves_word_count (text : String) (h : text ≠ "") :
  let result := arrange_words text
  (result.split (· = ' ')).length = (text.split (· = ' ')).length := sorry
-- </vc-theorems>