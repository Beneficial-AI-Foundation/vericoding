-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def top_3_words (s : String) : List String := sorry 

theorem empty_string_returns_empty_list :
  top_3_words "" = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem space_returns_empty_list :
  top_3_words " " = [] := sorry

theorem special_chars_return_empty_list (s : String) :
  (∀ c ∈ s.data, !c.isAlpha ∧ c ≠ '\'') → 
  top_3_words s = [] := sorry

theorem simple_word_count :
  top_3_words "aaa bbb aaa ccc bbb aaa" = ["aaa", "bbb", "ccc"] := sorry

theorem case_insensitive_count :
  top_3_words "AAA bbb AAA ccc BBB aaa" = ["aaa", "bbb", "ccc"] := sorry

theorem valid_apostrophes :
  top_3_words "can't won't don't can't won't can't" = ["can't", "won't", "don't"] := sorry
-- </vc-theorems>