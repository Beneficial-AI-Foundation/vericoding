-- <vc-helpers>
-- </vc-helpers>

def MOD : Nat := 998244353

def solve_ipl_rooms (p q r : Nat) : Nat :=
  sorry

theorem output_in_valid_range (p q r : Nat) (h1 : p > 0) (h2 : q > 0) (h3 : r > 0) :
  let result := solve_ipl_rooms p q r
  0 ≤ result ∧ result < MOD :=
sorry

theorem empty_when_insufficient_rooms (p q r : Nat) (h1 : p > 0) (h2 : q > 0) (h3 : r > 0) :
  p + q/2 < r → solve_ipl_rooms p q r = 0 :=
sorry

theorem symmetric_case (n : Nat) (h : n > 0) :
  solve_ipl_rooms n n 1 = solve_ipl_rooms n n 1 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_ipl_rooms 2 1 4

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_ipl_rooms 2 4 4

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_ipl_rooms 2 5 4

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible