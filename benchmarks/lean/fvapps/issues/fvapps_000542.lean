-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_professor_scores (n m : Nat) (questions : List (Nat × Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_nonnegative (n m : Nat) (questions : List (Nat × Nat × Nat)) :
  solve_professor_scores n m questions ≥ 0 := sorry

theorem result_bounded_by_max (n m : Nat) (questions : List (Nat × Nat × Nat)) :
  solve_professor_scores n m questions ≤ 10 * (10 ^ questions.length) := sorry

theorem all_students_same_k (n k : Nat) :
  n > 0 → k > 0 → k ≤ 10 → solve_professor_scores n 1 [(1,n,k)] = 10 * k := sorry

end ProfessorScores

/-
info: 202
-/
-- #guard_msgs in
-- #eval solve_professor_scores 5 3 [(1, 3, 5), (2, 5, 2), (3, 4, 7)]

/-
info: 50
-/
-- #guard_msgs in
-- #eval solve_professor_scores 1 1 [(1, 1, 5)]

/-
info: 60
-/
-- #guard_msgs in
-- #eval solve_professor_scores 3 2 [(1, 3, 2), (1, 3, 3)]
-- </vc-theorems>