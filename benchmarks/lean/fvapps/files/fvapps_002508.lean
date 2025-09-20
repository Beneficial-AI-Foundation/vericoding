-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_student_averages (n_students : Nat) (n_subjects : Nat) (subject_marks : List String) : List Float := sorry

/- Main property theorems -/
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_student_averages_length
  (n_students : Nat) (n_subjects : Nat) (subject_marks : List String)
  (h1 : n_students > 0) (h2 : n_subjects > 0) :
  List.length (calculate_student_averages n_students n_subjects subject_marks) = n_students := sorry

theorem calculate_student_averages_bounds 
  (n_students : Nat) (n_subjects : Nat) (subject_marks : List String)
  (h1 : n_students > 0) (h2 : n_subjects > 0) :
  ∀ x ∈ calculate_student_averages n_students n_subjects subject_marks, 0 ≤ x ∧ x ≤ 100 := sorry

/- Special case theorems -/

theorem calculate_student_averages_zeros
  (n_students : Nat) (n_subjects : Nat)
  (h1 : n_students > 0) (h2 : n_subjects > 0)
  (subject_marks : List String)
  (h3 : subject_marks.length = n_subjects)
  (h4 : ∀ mark ∈ subject_marks, mark = String.intercalate " " (List.replicate n_students "0")) :
  ∀ x ∈ calculate_student_averages n_students n_subjects subject_marks, x = 0 := sorry

theorem calculate_student_averages_hundreds
  (n_students : Nat) (n_subjects : Nat)
  (h1 : n_students > 0) (h2 : n_subjects > 0)
  (subject_marks : List String)
  (h3 : subject_marks.length = n_subjects)
  (h4 : ∀ mark ∈ subject_marks, mark = String.intercalate " " (List.replicate n_students "100")) :
  ∀ x ∈ calculate_student_averages n_students n_subjects subject_marks, x = 100 := sorry

/- Consistency theorem for constant marks -/

theorem calculate_student_averages_consistency
  (n_students : Nat) (n_subjects : Nat) (marks : List Float)
  (h1 : n_students > 0) (h2 : n_subjects > 0) (h3 : marks.length > 0)
  (h4 : ∀ m ∈ marks, 0 ≤ m ∧ m ≤ 100)
  (subject_marks : List String) :
  ∀ i < n_students, ∃ result ∈ calculate_student_averages n_students n_subjects subject_marks, 
    Float.abs (result - marks[i % marks.length]'(Nat.mod_lt _ h3)) ≤ 1e-9 := sorry
-- </vc-theorems>