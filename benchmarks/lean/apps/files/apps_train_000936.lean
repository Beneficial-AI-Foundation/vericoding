-- <vc-helpers>
-- </vc-helpers>

def solve_candy_distribution (n k : Nat) : Nat × Nat := sorry

theorem candy_distribution_non_negative (n k : Nat) :
  let (candies_per_student, remaining) := solve_candy_distribution n k
  candies_per_student ≥ 0 ∧ remaining ≥ 0 := sorry

theorem remaining_less_than_students {n k : Nat} (h : k > 0) :
  let (candies_per_student, remaining) := solve_candy_distribution n k
  remaining < k := sorry

theorem total_candies_preserved {n k : Nat} (h : k > 0) :
  let (candies_per_student, remaining) := solve_candy_distribution n k
  n = candies_per_student * k + remaining := sorry

theorem zero_students_case (n : Nat) :
  let (candies_per_student, remaining) := solve_candy_distribution n 0
  candies_per_student = 0 ∧ remaining = n := sorry

theorem perfect_division (n k : Nat) (h : k > 0) :
  let (candies_per_student, remaining) := solve_candy_distribution (n * k) k
  candies_per_student = n ∧ remaining = 0 := sorry

/-
info: (5, 0)
-/
-- #guard_msgs in
-- #eval solve_candy_distribution 10 2

/-
info: (33, 1)
-/
-- #guard_msgs in
-- #eval solve_candy_distribution 100 3

/-
info: (0, 7)
-/
-- #guard_msgs in
-- #eval solve_candy_distribution 7 0

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible