-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_correct_spellings (dict_words : List String) (misspelled : List String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_misspelled_returns_empty {dict_words : List String} :
  find_correct_spellings dict_words [] = [] :=
  sorry

theorem empty_dict_returns_empty {misspelled : List String} :
  find_correct_spellings [] misspelled = [] :=
  sorry

theorem exact_matches_returned {words : List String} (w : String) :
  w ∈ words → w ∈ find_correct_spellings words words :=
  sorry
-- </vc-theorems>