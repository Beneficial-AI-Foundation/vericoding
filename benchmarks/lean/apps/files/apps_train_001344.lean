def solve_cheat_possibilities (a b : Nat) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def countDivisors (n : Nat) : Nat :=
  sorry

theorem same_numbers_returns_negative_one 
  {x : Nat} (h : x > 0) (h2 : x ≤ 1000) :
  solve_cheat_possibilities x x = -1 := 
  sorry

theorem result_is_symmetric
  {a b : Nat} (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 1000) (h4 : b ≤ 1000) :
  solve_cheat_possibilities a b = solve_cheat_possibilities b a :=
  sorry

theorem result_is_nonnegative_for_different
  {a b : Nat} (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 1000) (h4 : b ≤ 1000) (h5 : a ≠ b) :
  solve_cheat_possibilities a b ≥ 0 :=
  sorry

theorem perfect_squares_have_odd_factors
  {n : Nat} (h1 : n > 0) (h2 : n ≤ 100) :
  solve_cheat_possibilities 0 (n * n) % 2 = 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_cheat_possibilities 2 6

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_cheat_possibilities 5 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_cheat_possibilities 10 14

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible