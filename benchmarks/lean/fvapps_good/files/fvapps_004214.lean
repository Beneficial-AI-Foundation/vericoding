-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_haiku (text : String) : Bool := sorry

def make_line (syllables : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wrong_lines_not_haiku
  {ls : List String}
  (h : ls.length ≠ 3) :
  is_haiku (String.intercalate "\n" ls) = false := sorry

theorem wrong_syllable_pattern
  (s1 s2 s3 : Nat)
  (h : (s1, s2, s3) ≠ (5, 7, 5)) :
  is_haiku (make_line s1 ++ "\n" ++ make_line s2 ++ "\n" ++ make_line s3) = false := sorry

theorem correct_syllable_pattern :
  is_haiku (make_line 5 ++ "\n" ++ make_line 7 ++ "\n" ++ make_line 5) = true := sorry
-- </vc-theorems>