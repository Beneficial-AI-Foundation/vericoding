def String.isAlpha : Char → Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def changer : String → String :=
  sorry

theorem changer_length (s : String) :
  s.length = (changer s).length :=
  sorry

theorem changer_nonalpha_unchanged {s : String} {i : String.Pos} {c : Char} :
  c = s.get i → ¬(String.isAlpha c) → (changer s).get i = c :=
  sorry

theorem changer_empty :
  changer "" = "" :=
  sorry

theorem changer_boundary_case :
  changer "abcxyz" = "bcdyzA" :=
  sorry

/-
info: 'dbU30'
-/
-- #guard_msgs in
-- #eval changer "Cat30"

/-
info: 'Ifmmp xpsmE'
-/
-- #guard_msgs in
-- #eval changer "Hello World"

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval changer "z"

-- Apps difficulty: introductory
-- Assurance level: unguarded