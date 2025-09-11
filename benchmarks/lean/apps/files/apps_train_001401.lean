-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_robot_cake_distribution (n : Nat) (m : Nat) : String := sorry

theorem robot_cake_distribution_bounds (n m : Nat)
  (h1 : 2 ≤ n)
  (h2 : n ≤ 100)
  (h3 : m < n) :
  let result := solve_robot_cake_distribution n m
  (result = "Yes" ∨ ∃ count, result = s!"No {count}" ∧ 1 ≤ count ∧ count < n) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem robot_cake_zero_shift (n : Nat)
  (h1 : 2 ≤ n)
  (h2 : n ≤ 100) :
  solve_robot_cake_distribution n 0 = "No 1" := sorry

theorem robot_cake_count_validity (n m : Nat)
  (h1 : 2 ≤ n)
  (h2 : n ≤ 100)
  (h3 : m < n) :
  let result := solve_robot_cake_distribution n m
  (result = "Yes" ∨ ∃ count, result = s!"No {count}" ∧ 0 < count ∧ count < n) := sorry

/-
info: 'No 1'
-/
-- #guard_msgs in
-- #eval solve_robot_cake_distribution 2 0

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval solve_robot_cake_distribution 2 1

/-
info: 'No 2'
-/
-- #guard_msgs in
-- #eval solve_robot_cake_distribution 4 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded