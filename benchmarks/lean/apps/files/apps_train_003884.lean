def String.count (s : String) (c : Char) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def added_char (base modified : String) : Char :=
  sorry

theorem added_char_correct (base : String) (c : Char) :
  let modified := base ++ String.mk (List.replicate 3 c)
  added_char base modified = c :=
sorry

theorem length_difference (base : String) (c : Char) :
  let modified := base ++ String.mk (List.replicate 3 c)
  modified.length = base.length + 3 :=
sorry

/-
info: 'c'
-/
-- #guard_msgs in
-- #eval added_char "hello" "checlclo"

/-
info: 'c'
-/
-- #guard_msgs in
-- #eval added_char "aabbcc" "aacccbbcc"

/-
info: '2'
-/
-- #guard_msgs in
-- #eval added_char "abcde" "2db2a2ec"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible