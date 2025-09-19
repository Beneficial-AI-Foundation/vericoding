-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pigLatin (s : String) : Option String := sorry

theorem pigLatin_valid_ends_ay 
  (s : String)
  (h : s.data.all Char.isAlpha ∧ s ≠ "") :
  (pigLatin s).map (·.endsWith "ay") = some true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pigLatin_valid_all_lower
  (s : String)
  (h : s.data.all Char.isAlpha ∧ s ≠ "") :
  (pigLatin s).map (·.data.all Char.isLower) = some true := sorry

theorem pigLatin_valid_length
  (s : String)
  (h : s.data.all Char.isAlpha ∧ s ≠ "") :
  (pigLatin s).map (fun r => r.length = s.length + 2 ∨ r.length = s.length + 3) = some true := sorry

theorem pigLatin_valid_contains_input_chars
  (s : String)
  (h : s.data.all Char.isAlpha ∧ s ≠ "") :
  (pigLatin s).map (fun r => s.data.all (fun c => (r.data.any (· = c.toLower)))) = some true := sorry

theorem pigLatin_invalid_input
  (s : String)
  (h : ¬s.data.all Char.isAlpha) :
  pigLatin s = none := sorry

theorem pigLatin_empty_input :
  pigLatin "" = none := sorry
-- </vc-theorems>