-- <vc-helpers>
-- </vc-helpers>

def count_char (s : String) (c : Char) : Nat :=
  sorry

theorem count_char_case_insensitive_char (s : String) (c : Char) :
  count_char s c = count_char s c.toUpper ∧ 
  count_char s c = count_char s c.toLower :=
sorry

theorem count_char_bounds (s : String) (c : Char) :
  0 ≤ count_char s c ∧ count_char s c ≤ s.length :=
sorry 

theorem count_char_case_insensitive_string (s : String) (c : Char) :
  count_char s c = count_char s.toUpper c ∧
  count_char s c = count_char s.toLower c :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_char "fizzbuzz" "z"

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_char "Fancy fifth fly aloof" "f"

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_char "Hello World" "l"

-- Apps difficulty: introductory
-- Assurance level: guarded