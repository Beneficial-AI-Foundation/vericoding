-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spacey (words : List String) : List String := sorry

theorem length_matches_input (words : List String) 
  (h : words ≠ []) :
  (spacey words).length = words.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem contains_all_previous_words (words : List String) 
  (h : words ≠ []) 
  (i : Nat)
  (hlt : i < (spacey words).length) :
  ((spacey words)[i]'hlt) = String.join (words.take (i+1)) := sorry

theorem lengths_monotonic (words : List String)
  (h : words ≠ [])
  (i : Nat)
  (hlt : i+1 < (spacey words).length) 
  (hlt2 : i < (spacey words).length) :
  ((spacey words)[i]'hlt2).length ≤ ((spacey words)[i+1]'hlt).length := sorry

theorem first_elem_matches (words : List String)
  (h : words ≠ []) 
  (h1 : 0 < (spacey words).length)
  (h2 : 0 < words.length) :
  ((spacey words)[0]'h1) = (words[0]'h2) := sorry

theorem last_elem_contains_all (words : List String)
  (h : words ≠ []) 
  (h1 : spacey words ≠ []) :
  (spacey words).getLast h1 = String.join words := sorry
-- </vc-theorems>