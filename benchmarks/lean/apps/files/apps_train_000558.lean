-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_training_camp (n m : Nat) : Nat := sorry 

theorem solve_training_camp_nonnegative (n m : Nat) :
  n ≥ 1 → solve_training_camp n m ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_training_camp_teacher_only (m : Nat) :
  solve_training_camp 1 m = 0 := sorry

theorem solve_training_camp_two_people (m : Nat) :
  solve_training_camp 2 m = m := sorry

theorem solve_training_camp_monotone_n (n m : Nat) : 
  n > 2 → solve_training_camp (n+1) m ≥ solve_training_camp n m := sorry

theorem solve_training_camp_monotone_m (n m : Nat) :
  n > 2 → m > 0 → solve_training_camp n m ≥ solve_training_camp n (m-1) := sorry

theorem solve_training_camp_zero_topics_teacher (n : Nat) :
  n = 1 → solve_training_camp n 0 = 0 := sorry

theorem solve_training_camp_zero_topics_two (n : Nat) :
  n = 2 → solve_training_camp n 0 = 0 := sorry

theorem solve_training_camp_zero_topics_many (n : Nat) :
  n > 2 → solve_training_camp n 0 = n - 3 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_training_camp 2 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_training_camp 3 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_training_camp 1 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible