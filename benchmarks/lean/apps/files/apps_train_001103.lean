-- <vc-helpers>
-- </vc-helpers>

def solve_order (p : Nat) (idx : Nat) : Nat := sorry

-- Result is within bounds for p bits

theorem solve_order_bounds (p : Nat) (idx : Nat) (h : idx < 2^p) : 
  solve_order p idx < 2^p := sorry

-- Result is involutive 

theorem solve_order_involution (p : Nat) (idx : Nat) (h : idx < 2^p) :
  solve_order p (solve_order p idx) = idx := sorry

-- Identity cases preserve 0 and max value

theorem solve_order_zero (p : Nat) :
  solve_order p 0 = 0 := sorry

theorem solve_order_max (p : Nat) :
  solve_order p (2^p - 1) = 2^p - 1 := sorry

-- Bits preservation

theorem solve_order_bits_preservation (p : Nat) (idx : Nat) (h : idx < 2^p) :
  ∃ k, solve_order p idx < 2^k ∧ k ≤ p := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_order 3 3

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_order 3 7

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_order 4 10

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible