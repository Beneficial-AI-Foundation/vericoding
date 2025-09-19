-- <vc-preamble>
def maxProfit (prices: List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxPairwiseDiff (prices: List Nat) : Nat :=
  match prices with
  | [] => 0
  | x::xs => match xs with
    | [] => 0
    | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxprofit_bounds_pair (a b: Nat) :
  maxProfit [a, b] = max 0 (b - a) :=
  sorry
-- </vc-theorems>