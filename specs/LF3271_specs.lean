-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def approx_root (n : Nat) : Float := sorry

theorem approx_root_close_to_actual (n : Nat) (h : n ≤ 1000000) : 
  (approx_root n - Float.sqrt (n.toFloat)).abs < 0.1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem approx_root_perfect_squares (n : Nat) (h : n ≤ 1000) :
  approx_root (n * n) = n.toFloat := sorry

theorem approx_root_bounds (n : Nat) (h : n ≤ 1000000) :
  Float.floor (Float.sqrt (n.toFloat)) ≤ approx_root n ∧ 
  approx_root n ≤ Float.floor (Float.sqrt (n.toFloat)) + 1 := sorry

theorem approx_root_precision (n : Nat) (h : n ≤ 1000000) :
  (approx_root n - approx_root n).abs < 0.00001 := sorry
-- </vc-theorems>