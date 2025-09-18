-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def noSpace (s : String) : String := sorry

theorem no_space_no_spaces_in_result (s : String) :
  ¬(noSpace s).contains ' ' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_space_preserves_non_spaces (s : String) :
  noSpace s = s.replace (String.mk [' ']) "" := sorry

theorem no_space_identity_for_spaceless (s : String) :
  ¬s.contains ' ' → noSpace s = s := sorry

theorem no_space_empty :
  noSpace "" = "" := sorry
-- </vc-theorems>