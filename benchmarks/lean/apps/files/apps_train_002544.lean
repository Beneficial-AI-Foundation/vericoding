-- <vc-helpers>
-- </vc-helpers>

def tv_remote (s : String) : Nat := sorry

theorem tv_remote_non_negative (word : String) : 
  tv_remote word ≥ 0 := sorry

theorem tv_remote_greater_than_length (word : String) : 
  tv_remote word ≥ word.length := sorry 

theorem tv_remote_empty_zero : 
  tv_remote "" = 0 := sorry

theorem tv_remote_case_sensitive (word : String) : 
  (∃ c ∈ word.data, c.isAlpha) → 
  tv_remote (word.map Char.toUpper) ≠ tv_remote (word.map Char.toLower) := sorry

theorem tv_remote_spaces (spaces : String) : 
  (∀ c ∈ spaces.data, c = ' ') → 
  spaces.length > 0 → 
  tv_remote spaces ≥ spaces.length := sorry

/-
info: 49
-/
-- #guard_msgs in
-- #eval tv_remote "Code Wars"

/-
info: 0
-/
-- #guard_msgs in
-- #eval tv_remote ""

/-
info: 5
-/
-- #guard_msgs in
-- #eval tv_remote "   "

-- Apps difficulty: introductory
-- Assurance level: unguarded