-- <vc-helpers>
-- </vc-helpers>

def combine_names (first last : String) : String := sorry

theorem combine_names_type (first last : String) :
  first.length > 0 → last.length > 0 →
  combine_names first last = combine_names first last :=
sorry

theorem combine_names_starts_ends (first last : String) :
  first.length > 0 → last.length > 0 →
  String.startsWith (combine_names first last) first ∧
  String.endsWith (combine_names first last) last :=
sorry

theorem combine_names_space_count (first last : String) :
  first.length > 0 → last.length > 0 →
  String.length (String.replace (combine_names first last) " " "") + 1 = 
  String.length (combine_names first last) :=
sorry

theorem combine_names_length (first last : String) :
  first.length > 0 → last.length > 0 →
  String.length (combine_names first last) = String.length first + String.length last + 1 :=
sorry

/-
info: 'James Stevens'
-/
-- #guard_msgs in
-- #eval combine_names "James" "Stevens"

/-
info: 'Davy Back'
-/
-- #guard_msgs in
-- #eval combine_names "Davy" "Back"

/-
info: 'Arthur Dent'
-/
-- #guard_msgs in
-- #eval combine_names "Arthur" "Dent"

-- Apps difficulty: introductory
-- Assurance level: unguarded