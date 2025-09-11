-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_candies (r g b : Nat) : Nat := sorry

theorem solve_candies_non_negative (r g b : Nat) : 
  solve_candies r g b ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_candies_bounded_by_pairs (r g b : Nat) :
  solve_candies r g b ≤ r + g ∧ 
  solve_candies r g b ≤ r + b ∧
  solve_candies r g b ≤ g + b := sorry

theorem solve_candies_bounded_by_half_total (r g b : Nat) :
  solve_candies r g b ≤ (r + g + b) / 2 := sorry 

theorem solve_candies_returns_nat (r g b : Nat) :
  solve_candies r g b = (solve_candies r g b : Nat) := sorry

theorem solve_equal_piles (n : Nat) :
  solve_candies n n n = min (n + n) ((3 * n) / 2) := sorry

theorem solve_two_equal_piles (n m : Nat) :
  solve_candies n n m = min (n + n) (min (n + m) ((2 * n + m) / 2)) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_candies 1 1 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_candies 1 2 1

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_candies 7 4 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible