def maxProfit (prices: List Nat) : Nat :=
  sorry

def maxPairwiseDiff (prices: List Nat) : Nat :=
  match prices with
  | [] => 0
  | x::xs => match xs with
    | [] => 0
    | _ => sorry

theorem maxprofit_bounds_pair (a b: Nat) :
  maxProfit [a, b] = max 0 (b - a) :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible

/--
info: 7
-/
#guard_msgs in
#eval maxProfit [7, 1, 5, 3, 6, 4]

/--
info: 4
-/
#guard_msgs in
#eval maxProfit [1, 2, 3, 4, 5]

/--
info: 0
-/
#guard_msgs in
#eval maxProfit [7, 6, 4, 3, 1]