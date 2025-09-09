-- <vc-helpers>
-- </vc-helpers>

def solve_division_pairs (p q : Nat) : Nat :=
sorry

theorem division_pairs_divides (p q result : Nat) 
  (h1 : result = solve_division_pairs p q) :
  p % result = 0 := by
sorry

theorem division_pairs_le_p (p q result : Nat)
  (h1 : result = solve_division_pairs p q) :
  result ≤ p := by
sorry

theorem division_pairs_indivisible (p q result : Nat) 
  (h1 : result = solve_division_pairs p q)
  (h2 : p % q ≠ 0) : 
  result = p := by
sorry

theorem division_pairs_positive (p q result : Nat)
  (h1 : result = solve_division_pairs p q)
  (h2 : p > 0)
  (h3 : q > 0) :
  result > 0 := by
sorry

theorem division_pairs_identical (p : Nat)
  (h1 : p % 2 = 0)
  (h2 : p > 0) :
  solve_division_pairs p p = p / 2 := by
sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_division_pairs 10 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_division_pairs 12 6

/-
info: 179
-/
-- #guard_msgs in
-- #eval solve_division_pairs 179 822

/-
info: 1048576
-/
-- #guard_msgs in
-- #eval solve_division_pairs 42034266112 80174

/-
info: 114141144
-/
-- #guard_msgs in
-- #eval solve_division_pairs 228282288 228282288

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_division_pairs 1 323

-- Apps difficulty: competition
-- Assurance level: guarded