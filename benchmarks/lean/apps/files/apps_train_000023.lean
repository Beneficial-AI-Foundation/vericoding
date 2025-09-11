-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_elections (n : Nat) (voters : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_elections_nonnegative (n : Nat) (voters : List (Nat × Nat)) :
  solve_elections n voters ≥ 0 :=
sorry

theorem solve_elections_upper_bound (n : Nat) (voters : List (Nat × Nat)) :
  solve_elections n voters ≤ List.foldl (λ acc (pair : Nat × Nat) => acc + pair.2) 0 voters :=
sorry

theorem solve_elections_zero_votes (n : Nat) (voters : List (Nat × Nat)) :
  (List.all voters (λ pair => pair.1 = 0)) →
  solve_elections n voters = 0 :=
sorry

theorem solve_elections_single_zero_vote :
  solve_elections 1 [(0, 5)] = 0 :=
sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_elections 3 [(1, 5), (2, 10), (2, 8)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_elections 7 [(0, 1), (3, 1), (1, 1), (6, 1), (1, 1), (4, 1), (4, 1)]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_elections 6 [(2, 6), (2, 3), (2, 8), (2, 7), (4, 4), (5, 5)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded