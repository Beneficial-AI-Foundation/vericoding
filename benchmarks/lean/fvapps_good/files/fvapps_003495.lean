-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_constructing (src t : String) : Nat := sorry

theorem empty_target_returns_zero (src : String) :
  string_constructing src "" = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem known_case_three :
  string_constructing "abcdefgh" "hgfedcba" = 64 := sorry

theorem single_char_identity (c : Char) :
  string_constructing (String.mk [c]) (String.mk [c]) = 1 := sorry
-- </vc-theorems>