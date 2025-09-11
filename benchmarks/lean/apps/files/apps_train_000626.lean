-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_chocolate_distribution (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chocolate_distribution_bounds {n k : Nat} (n_pos : n > 0):
  let result := solve_chocolate_distribution n k
  result ≥ 0 ∧ result ≤ 2*n-1
  := sorry

theorem zero_chocolates {n : Nat} (n_pos : n > 0):
  solve_chocolate_distribution n 0 = 0
  := sorry 

theorem perfect_distribution {n : Nat} (n_pos : n > 0):
  ∀ m : Nat, solve_chocolate_distribution n (n * m) = 0
  := sorry

theorem edge_cases_bounds :
  ∀ n k : Nat,
  n > 0 →
  let result := solve_chocolate_distribution n k
  result ≥ 0 ∧ result ≤ 2*n-1
  := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_chocolate_distribution 3 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_chocolate_distribution 2 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_chocolate_distribution 3 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible