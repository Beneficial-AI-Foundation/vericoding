-- <vc-helpers>
-- </vc-helpers>

def mirror (s : String) (alphabet : String := "abcdefghijklmnopqrstuvwxyz") : String := sorry

theorem double_mirror_returns_original (s : String) :
  mirror (mirror s) = s.toLower := sorry

theorem mirror_identity_with_empty_chars (s : String) :
  mirror s "" = s.toLower := sorry

theorem empty_string_mirror :
  mirror "" = "" ∧ mirror "" "" = "" := sorry

theorem mirror_preserves_non_mapped_chars :
  mirror "123!@#" "abc" = "123!@#" := sorry

theorem basic_mirror :
  mirror "abcxyz" = "zyxcba" := sorry

/-
info: 'dvoxlnv slnv'
-/
-- #guard_msgs in
-- #eval mirror "Welcome home"

/-
info: 'adllo'
-/
-- #guard_msgs in
-- #eval mirror "hello" "abcdefgh"

/-
info: 'this is a secret'
-/
-- #guard_msgs in
-- #eval mirror "gsrh rh z hvxivg"

-- Apps difficulty: introductory
-- Assurance level: unguarded