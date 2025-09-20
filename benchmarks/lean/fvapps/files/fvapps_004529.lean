-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def GradeString : Type := String
deriving Inhabited

def grade_val (v : GradeString) : Int :=
  sorry

def sort_grades (grades : List GradeString) : List GradeString :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>