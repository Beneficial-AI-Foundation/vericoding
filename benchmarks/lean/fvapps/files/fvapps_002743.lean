-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cumulative_triangle (n : Nat) : Nat := sorry

theorem cumulative_triangle_positive (n : Nat) (h : n > 0) :
  cumulative_triangle n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cumulative_triangle_strictly_increasing (n : Nat) (h : n > 1) :
  cumulative_triangle n > cumulative_triangle (n - 1) := sorry
-- </vc-theorems>