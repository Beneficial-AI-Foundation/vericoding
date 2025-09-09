-- <vc-helpers>
-- </vc-helpers>

def solve_jams (n : Nat) (jams : List Nat) : Nat :=
sorry

theorem solve_jams_non_negative (n : Nat) (jams : List Nat) :
  n > 0 → jams.length = 2*n → solve_jams n jams ≥ 0 :=
sorry

theorem solve_jams_upper_bound (n : Nat) (jams : List Nat) :
  n > 0 → jams.length = 2*n → solve_jams n jams ≤ 2*n :=
sorry

theorem solve_jams_all_ones (n : Nat) :
  n > 0 → solve_jams n (List.replicate (2*n) 1) = 2*n :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_jams 6 [1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_jams 2 [1, 2, 1, 2]

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_jams 3 [1, 1, 1, 1, 1, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded