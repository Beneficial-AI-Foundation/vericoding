def GradeString : Type := String
deriving Inhabited

def grade_val (v : GradeString) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sort_grades (grades : List GradeString) : List GradeString :=
  sorry

theorem sort_preserves_size (grades : List GradeString) :
  List.length (sort_grades grades) = List.length grades :=
  sorry

theorem sort_preserves_elements (grades : List GradeString) (g : GradeString) :
  g ∈ grades ↔ g ∈ sort_grades grades :=
  sorry

theorem sort_is_ordered (grades : List GradeString) :
  ∀ i : Nat, i + 1 < List.length (sort_grades grades) →
  grade_val (List.get! (sort_grades grades) i) ≤ 
  grade_val (List.get! (sort_grades grades) (i + 1)) :=
  sorry

theorem empty_list_sort :
  sort_grades [] = [] :=
  sorry

theorem sort_idempotent (grades : List GradeString) :
  sort_grades (sort_grades grades) = sort_grades grades :=
  sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval sort_grades []

/-
info: ['VB', 'V0', 'V1', 'V3']
-/
-- #guard_msgs in
-- #eval sort_grades ["V1", "VB", "V3", "V0"]

/-
info: ['V0+', 'V1', 'V2']
-/
-- #guard_msgs in
-- #eval sort_grades ["V0+", "V2", "V1"]

-- Apps difficulty: introductory
-- Assurance level: unguarded