-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) : Nat :=
  sorry

-- Even and non-negative output for valid input
-- </vc-definitions>

-- <vc-theorems>
theorem solve_positive_even {n : Nat} (h : n ≥ 2) : 
  solve n ≥ 0 ∧ solve n % 2 = 0 :=
sorry

-- Monotonically increasing for n ≥ 4

theorem solve_monotonic {n : Nat} (h : n ≥ 4) :
  solve n ≥ solve (n - 2) :=
sorry

-- Special case for doubled perfect squares

theorem solve_perfect_squares {n : Nat} :
  ∀ x, n = 2 * (x * x) → solve n = 2 * x :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve 16

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 4

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve 36
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded