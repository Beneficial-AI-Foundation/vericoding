-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def withdraw (n : Int) : (Int × Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem withdraw_valid (amount : Int) (h : amount ≥ 20) (h2 : amount % 10 = 0) :
  let (hundreds, fifties, twenties) := withdraw amount
  hundreds ≥ 0 ∧ fifties ≥ 0 ∧ twenties ≥ 0 ∧
  hundreds * 100 + fifties * 50 + twenties * 20 = amount :=
sorry

theorem withdraw_optimal (amount : Int) (h : amount ≥ 20) (h2 : amount % 10 = 0) :
  let (hundreds, fifties, twenties) := withdraw amount
  twenties ≤ 4 :=
sorry

theorem withdraw_fifty_efficient (amount : Int) (h : amount ≥ 20) (h2 : amount % 10 = 0) :
  let (hundreds, fifties, twenties) := withdraw amount
  fifties > 0 →
  let remainder := amount - (hundreds * 100 + fifties * 50)
  remainder ≥ 0 ∧ remainder % 20 = 0 :=
sorry
-- </vc-theorems>