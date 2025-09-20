-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def adjust (coin price : Int) : Int := sorry

theorem adjust_multiple (coin price : Int) (h : coin > 0) : 
  (adjust coin price) % coin = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem adjust_greater_equal (coin price : Int) (h : coin > 0) :
  adjust coin price ≥ price := sorry

theorem adjust_minimal (coin price : Int) (h : coin > 0) :
  adjust coin price - coin < price := sorry

theorem adjust_idempotent (coin price : Int) (h : coin > 0) :
  adjust coin (adjust coin price) = adjust coin price := sorry
-- </vc-theorems>