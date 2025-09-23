-- <vc-preamble>
def List.sum (l : List Nat) : Nat :=
  l.foldl (· + ·) 0

def List.sort (l : List Nat) : List Nat :=
  sorry

def List.perm (l1 l2 : List Nat) : Prop :=
  sorry

def List.takeNth (l : List Nat) (n : Nat) : List Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxCoins (piles : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxcoins_minimal :
  maxCoins [1,1,1] = 1 :=
sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval maxCoins [2, 4, 1, 2, 7, 8]

/-
info: 4
-/
-- #guard_msgs in
-- #eval maxCoins [2, 4, 5]

/-
info: 18
-/
-- #guard_msgs in
-- #eval maxCoins [9, 8, 7, 6, 5, 1, 2, 3, 4]
-- </vc-theorems>