-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem power_of_10_boundary (m : Nat) (h : 0 < m) (h2 : m ≤ 100) :
  ∀ i : Nat, 1 ≤ i → i < 5 →
  solve_frodo_ship m (10^i - 1) = (m*i, m) :=
sorry

theorem between_powers (m : Nat) (exp : Nat)
  (h1 : 0 < m) (h2 : m ≤ 10)
  (h3 : 0 < exp) (h4 : exp ≤ 4) :
  solve_frodo_ship m (10^exp - 2) = (m*(exp-1), m) :=
sorry

/-
info: (1, 1)
-/
-- #guard_msgs in
-- #eval solve_frodo_ship 1 9

/-
info: (4, 2)
-/
-- #guard_msgs in
-- #eval solve_frodo_ship 2 99

/-
info: (9, 3)
-/
-- #guard_msgs in
-- #eval solve_frodo_ship 3 999
-- </vc-theorems>