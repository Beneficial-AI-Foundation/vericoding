-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n: Nat) : Nat := sorry

theorem sqrt_nonnegative (x : Nat) : sqrt x ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sqrt_squared_under (x : Nat) : sqrt x * sqrt x ≤ x := sorry

theorem sqrt_plus_one_squared_over (x : Nat) :
  sqrt x < 2^31 → (sqrt x + 1) * (sqrt x + 1) > x := sorry

theorem sqrt_round_trip (x : Nat) : 
  x ≤ 1000 → sqrt (x * x) = x := sorry
-- </vc-theorems>