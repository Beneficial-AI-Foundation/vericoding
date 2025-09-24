-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_order (p : Nat) (idx : Nat) : Nat := sorry

-- Result is within bounds for p bits
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>