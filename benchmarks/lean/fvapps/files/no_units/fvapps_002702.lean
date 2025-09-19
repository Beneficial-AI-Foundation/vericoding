-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def withdraw (n : Int) : (Int × Int × Int) := sorry

/- The withdraw function returns a valid solution for multiples of 10 -/
-- </vc-definitions>

-- <vc-theorems>
theorem withdraw_valid (amount : Int) (h : amount ≥ 20) (h2 : amount % 10 = 0) : 
  let (hundreds, fifties, twenties) := withdraw amount
  hundreds ≥ 0 ∧ fifties ≥ 0 ∧ twenties ≥ 0 ∧ 
  hundreds * 100 + fifties * 50 + twenties * 20 = amount := sorry
-- </vc-theorems>