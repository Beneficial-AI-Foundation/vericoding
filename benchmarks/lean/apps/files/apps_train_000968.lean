-- <vc-helpers>
-- </vc-helpers>

def calculate_mean_scores (n m : Nat) (questions : List (Nat × Nat × Nat)) : Nat :=
  sorry

theorem empty_questions (n m : Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : m ≤ 10) :
  calculate_mean_scores n 0 [] = 10 := by
  sorry

theorem all_students_same_multiplier (n m k : Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : m ≤ 10) 
  (h3 : 1 ≤ k ∧ k ≤ 10) :
  calculate_mean_scores n 1 [(1, n, k)] = 10 * k := by
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded