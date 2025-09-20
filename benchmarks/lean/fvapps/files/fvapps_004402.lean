-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nextLetter (s : String) : String := sorry

-- Length preservation
-- </vc-definitions>

-- <vc-theorems>
theorem nextLetter_length_preserved (s : String) :
  (nextLetter s).length = s.length := sorry

-- Non-alphabetic character preservation 

theorem nextLetter_preserves_non_alpha (s : String) (pos : String.Pos) (h : pos.1 < s.length) :
  ¬(s.get! pos).isAlpha →
  (nextLetter s).get! pos = s.get! pos := sorry

-- Case preservation

theorem nextLetter_preserves_case (s : String) (pos : String.Pos) (h : pos.1 < s.length) :
  (s.get! pos).isAlpha →
  ((s.get! pos).isUpper = ((nextLetter s).get! pos).isUpper) ∧
  ((s.get! pos).isLower = ((nextLetter s).get! pos).isLower) := sorry

-- Shifts by one except for z/Z

theorem nextLetter_shifts_by_one (s : String) (pos : String.Pos) (h : pos.1 < s.length) :
  (s.get! pos).isAlpha →
  s.get! pos ≠ 'z' →
  s.get! pos ≠ 'Z' →
  ((nextLetter s).get! pos).toNat = (s.get! pos).toNat + 1 := sorry

-- z/Z wrapping

theorem nextLetter_wraps_z (s : String) (pos : String.Pos) (h : pos.1 < s.length) :
  s.get! pos = 'z' →
  (nextLetter s).get! pos = 'a' := sorry

theorem nextLetter_wraps_Z (s : String) (pos : String.Pos) (h : pos.1 < s.length) :
  s.get! pos = 'Z' →
  (nextLetter s).get! pos = 'A' := sorry
-- </vc-theorems>