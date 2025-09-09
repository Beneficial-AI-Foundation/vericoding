-- <vc-helpers>
-- </vc-helpers>

def noSpace (s : String) : String := sorry

theorem no_space_no_spaces_in_result (s : String) :
  ¬(noSpace s).contains ' ' := sorry

theorem no_space_preserves_non_spaces (s : String) :
  noSpace s = s.replace (String.mk [' ']) "" := sorry

theorem no_space_identity_for_spaceless (s : String) :
  ¬s.contains ' ' → noSpace s = s := sorry

theorem no_space_empty :
  noSpace "" = "" := sorry

/-
info: '8j8mBliB8gimjB8B8jlB'
-/
-- #guard_msgs in
-- #eval no_space "8 j 8   mBliB8g  imjB8B8  jl  B"

/-
info: '88Bifk8hB8BB8BBBB888chl8BhBfd'
-/
-- #guard_msgs in
-- #eval no_space "8 8 Bi fk8h B 8 BB8B B B  B888 c hl8 BhB fd"

/-
info: '8jaam'
-/
-- #guard_msgs in
-- #eval no_space "8j aam"

-- Apps difficulty: introductory
-- Assurance level: unguarded