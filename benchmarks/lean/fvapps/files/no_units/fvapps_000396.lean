-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ladder_length (begin_word end_word : String) (word_list : List String) : Nat := sorry

-- Result should always be non-negative
-- </vc-definitions>

-- <vc-theorems>
theorem ladder_length_nonnegative 
  (begin_word end_word : String) (word_list : List String) :
  ladder_length begin_word end_word word_list ≥ 0 := sorry

-- If end_word not in word_list, result should be 0 

theorem ladder_length_zero_when_not_in_list
  (begin_word end_word : String) (word_list : List String) :
  ¬(end_word ∈ word_list) → ladder_length begin_word end_word word_list = 0 := sorry

-- If words differ by one letter and end_word in word_list, result should be 2

theorem ladder_length_two_when_one_diff
  (begin_word end_word : String) (word_list : List String) :
  end_word ∈ word_list →
  (begin_word.length = end_word.length) →
  ((List.zip begin_word.data end_word.data).filter (fun p => p.1 ≠ p.2)).length = 1 →
  ladder_length begin_word end_word word_list = 2 := sorry

-- If words have different lengths, result should be 0

theorem ladder_length_zero_when_different_lengths
  (begin_word end_word : String) (word_list : List String) :
  begin_word.length ≠ end_word.length →
  ladder_length begin_word end_word word_list = 0 := sorry
-- </vc-theorems>