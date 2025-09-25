-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def show_me (s : String) : Bool := sorry

theorem show_me_empty :
  show_me "" = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem show_me_single_letter (c : Char) :
  show_me (String.singleton c) = false := sorry

theorem show_me_invalid_casing {s : String} (h1 : s.length ≥ 2) :
  (¬s.front.isUpper ∨ ¬(s.drop 1).all Char.isLower) →
  show_me s = false := sorry

theorem show_me_invalid_chars {s : String} :
  s.length > 0 →
  (∃ c ∈ s.data, ¬(c.isUpper ∨ c.isLower)) →
  show_me s = false := sorry
-- </vc-theorems>