-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxProfit (prices: List Nat) : Nat :=
  sorry

def maxPairwiseDiff (prices: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxprofit_bounds_pair (a b: Nat) :
  maxProfit [a, b] = max 0 (b - a) :=
  sorry
-- </vc-theorems>