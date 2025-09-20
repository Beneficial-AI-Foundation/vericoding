-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_grade (s1 s2 s3 : Int) : Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_grade_valid_output (s1 s2 s3 : Int) (h1 : 0 ≤ s1 ∧ s1 ≤ 100) 
    (h2 : 0 ≤ s2 ∧ s2 ≤ 100) (h3 : 0 ≤ s3 ∧ s3 ≤ 100) :
  let grade := get_grade s1 s2 s3
  grade = 'A' ∨ grade = 'B' ∨ grade = 'C' ∨ grade = 'D' ∨ grade = 'F' :=
  sorry

theorem get_grade_A (s1 s2 s3 : Int) (h1 : 0 ≤ s1 ∧ s1 ≤ 100)
    (h2 : 0 ≤ s2 ∧ s2 ≤ 100) (h3 : 0 ≤ s3 ∧ s3 ≤ 100)
    (avg : (s1 + s2 + s3) / 3 ≥ 90) :
  get_grade s1 s2 s3 = 'A' :=
  sorry

theorem get_grade_B (s1 s2 s3 : Int) (h1 : 0 ≤ s1 ∧ s1 ≤ 100)
    (h2 : 0 ≤ s2 ∧ s2 ≤ 100) (h3 : 0 ≤ s3 ∧ s3 ≤ 100)
    (avg : (s1 + s2 + s3) / 3 ≥ 80 ∧ (s1 + s2 + s3) / 3 < 90) :
  get_grade s1 s2 s3 = 'B' :=
  sorry

theorem get_grade_C (s1 s2 s3 : Int) (h1 : 0 ≤ s1 ∧ s1 ≤ 100)
    (h2 : 0 ≤ s2 ∧ s2 ≤ 100) (h3 : 0 ≤ s3 ∧ s3 ≤ 100)
    (avg : (s1 + s2 + s3) / 3 ≥ 70 ∧ (s1 + s2 + s3) / 3 < 80) :
  get_grade s1 s2 s3 = 'C' :=
  sorry

theorem get_grade_D (s1 s2 s3 : Int) (h1 : 0 ≤ s1 ∧ s1 ≤ 100)
    (h2 : 0 ≤ s2 ∧ s2 ≤ 100) (h3 : 0 ≤ s3 ∧ s3 ≤ 100)
    (avg : (s1 + s2 + s3) / 3 ≥ 60 ∧ (s1 + s2 + s3) / 3 < 70) :
  get_grade s1 s2 s3 = 'D' :=
  sorry

theorem get_grade_F (s1 s2 s3 : Int) (h1 : 0 ≤ s1 ∧ s1 ≤ 100)
    (h2 : 0 ≤ s2 ∧ s2 ≤ 100) (h3 : 0 ≤ s3 ∧ s3 ≤ 100)
    (avg : (s1 + s2 + s3) / 3 < 60) :
  get_grade s1 s2 s3 = 'F' :=
  sorry
-- </vc-theorems>