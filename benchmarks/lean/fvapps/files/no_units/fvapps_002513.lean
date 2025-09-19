-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swapCase (s : String) : String := sorry

theorem swapCase_preserves_non_letters (s : String)
  (h : ∀ c ∈ s.data, ¬(c.isUpper ∨ c.isLower)) :
  swapCase s = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swapCase_ascii_letters_upper (s : String) (c : Char)
  (h1 : c ∈ s.data) (h2 : c.isUpper) :
  ∀ i, (swapCase s).data.get! i ≠ c := sorry

theorem swapCase_ascii_letters_lower (s : String) (c : Char)
  (h1 : c ∈ s.data) (h2 : c.isLower) :
  ∀ i, (swapCase s).data.get! i ≠ c := sorry

theorem swapCase_preserves_empty (s : String)
  (h : s = "") :
  swapCase s = s := sorry

theorem swapCase_preserves_whitespace (s : String)
  (h : ∀ c ∈ s.data, c.isWhitespace) :
  swapCase s = s := sorry
-- </vc-theorems>