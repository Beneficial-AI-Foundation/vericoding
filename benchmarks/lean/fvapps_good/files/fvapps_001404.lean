-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def analyze_grade_periods (grades : List Nat) (queries : List (Nat × Nat)) : List Nat :=
  sorry

-- Length of results matches length of queries
-- </vc-definitions>

-- <vc-theorems>
theorem analyze_grade_periods_length_match 
  (grades : List Nat) (queries : List (Nat × Nat))
  (h : grades.length > 0) :
  (analyze_grade_periods grades queries).length = queries.length :=
sorry

-- Results are non-negative

theorem analyze_grade_periods_nonneg 
  (grades : List Nat) (queries : List (Nat × Nat))
  (h : grades.length > 0) :
  ∀ r ∈ analyze_grade_periods grades queries, r ≥ 0 :=
sorry

-- Single element ranges give 0

theorem analyze_grade_periods_single_elem
  (grades : List Nat) (l r : Nat)
  (h1 : grades.length > 0)
  (h2 : l ≤ grades.length)
  (h3 : r ≤ grades.length)
  (h4 : l = r) :
  analyze_grade_periods grades [(l,r)] = [0] :=
sorry

-- Constant sequences give 0

theorem analyze_grade_periods_constant_seq
  (val len : Nat)
  (h1 : len > 0)
  (h2 : val > 0)
  (grades : List Nat)
  (h3 : grades = List.replicate len val) :
  analyze_grade_periods grades [(1,len)] = [0] :=
sorry

-- Result matches expected squared differences

theorem analyze_grade_periods_correct_calc
  (grades : List Nat) (l r : Nat)
  (h1 : grades.length > 0)
  (h2 : l ≤ grades.length)
  (h3 : r ≤ grades.length)
  (h4 : l ≤ r) :
  analyze_grade_periods grades [(l,r)] = 
    [List.foldl
      (λ acc i => acc + (grades[i+1]! - grades[i]!)^2)
      0
      (List.range (r-l))] :=
sorry
-- </vc-theorems>