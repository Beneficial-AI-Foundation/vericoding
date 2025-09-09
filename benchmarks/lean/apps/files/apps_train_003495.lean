-- <vc-helpers>
-- </vc-helpers>

def string_constructing (src t : String) : Nat := sorry

theorem empty_target_returns_zero (src : String) :
  string_constructing src "" = 0 := sorry

theorem known_case_three :
  string_constructing "abcdefgh" "hgfedcba" = 64 := sorry

theorem single_char_identity (c : Char) :
  string_constructing (String.mk [c]) (String.mk [c]) = 1 := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible