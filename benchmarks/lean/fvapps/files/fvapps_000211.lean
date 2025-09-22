-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isGoodArray (nums : List Nat) : Bool :=
sorry

def gcd (a b : Nat) : Nat :=
sorry

def listGcd (nums : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem good_array_gcd {nums : List Nat} (h : nums ≠ []) :
  isGoodArray nums = true ↔ listGcd nums = 1
  :=
sorry

theorem multiples_not_good {n : Nat} (h : n ≥ 2) :
  isGoodArray [n, 2*n, 3*n, 4*n] = false
  :=
sorry

theorem scale_makes_not_good {nums : List Nat} (h : nums ≠ []) :
  isGoodArray (nums.map (· * 2)) = false
  :=
sorry
-- </vc-theorems>