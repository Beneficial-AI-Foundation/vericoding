-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_perfect_square_pairs (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem perfect_square_pairs_non_negative {a b : Nat} : 
  find_perfect_square_pairs a b ≥ 0 :=
sorry

theorem perfect_square_pairs_monotonic_a {a b : Nat} (h : a > 0) :
  find_perfect_square_pairs (a-1) b ≤ find_perfect_square_pairs a b :=
sorry

theorem perfect_square_pairs_monotonic_b {a b : Nat} (h : b > 0) :
  find_perfect_square_pairs a (b-1) ≤ find_perfect_square_pairs a b :=
sorry

theorem perfect_square_pairs_zero_a {b : Nat} :
  find_perfect_square_pairs 0 b = 0 :=
sorry

theorem perfect_square_pairs_zero_b {a : Nat} :
  find_perfect_square_pairs a 0 = 0 :=
sorry

theorem perfect_square_pairs_zero_zero :
  find_perfect_square_pairs 0 0 = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_perfect_square_pairs 4 4

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_perfect_square_pairs 2 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_perfect_square_pairs 5 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded