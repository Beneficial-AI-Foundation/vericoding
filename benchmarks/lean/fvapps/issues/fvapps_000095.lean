-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_exam_problems (n : Nat) (T : Nat) (a : Nat) (b : Nat) (tasks : Tasks) (total_a total_b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_exam_problems_bounds {n T a b : Nat} {tasks : Tasks} {total_a total_b : Nat}
  (n_pos : n > 0) (T_pos : T > 0) (a_pos : a > 0) (b_pos : b > 0) :
  let result := solve_exam_problems n T a b tasks total_a total_b
  result ≤ total_a + total_b ∧ result ≥ 0 :=
sorry

theorem solve_empty_tasks {n T a b : Nat}
  (n_pos : n > 0) (T_pos : T > 0) (a_pos : a > 0) (b_pos : b > 0) :
  solve_exam_problems n T a b [] 0 0 = 0 :=
sorry

theorem solve_zero_time {n a b : Nat} {tasks : Tasks}
  (n_pos : n > 0) (a_pos : a > 0) (b_pos : b > 0) :
  solve_exam_problems n 0 a b tasks 1 0 = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_exam_problems 3 5 1 3 list(zip(t, types)) sum((1 for x in types if x == 0)) sum((1 for x in types if x == 1))

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_exam_problems 2 5 2 3 list(zip(t, types)) sum((1 for x in types if x == 0)) sum((1 for x in types if x == 1))

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_exam_problems 1 20 2 4 list(zip(t, types)) sum((1 for x in types if x == 0)) sum((1 for x in types if x == 1))
-- </vc-theorems>