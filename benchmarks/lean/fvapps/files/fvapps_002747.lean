-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find (s : String) : String := sorry

theorem single_char_strings (s : String) 
  (h : ∀ c ∈ s.data, c = '!') :
  find s = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_exclaim_question (s : String)
  (h : ∀ c ∈ s.data, c ≠ '!' ∧ c ≠ '?') :
  find s = "" := sorry

theorem result_only_valid_chars (s : String) :
  ∀ c ∈ (find s).data, c = '!' ∨ c = '?' := sorry
-- </vc-theorems>