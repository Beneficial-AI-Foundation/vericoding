-- <vc-preamble>
def max_profit (k : Nat) (prices : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lastElem (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | [x] => x
  | x::xs => lastElem xs
-- </vc-definitions>

-- <vc-theorems>
theorem single_price_zero_profit (k : Nat) (p : Nat) : 
  max_profit k [p] = 0 := sorry

private def pairwise_profits (prices : List Nat) : Nat :=
  sorry

private def isSorted (l : List Nat) : Prop :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_profit 2 [2, 4, 1]

/-
info: 7
-/
-- #guard_msgs in
-- #eval max_profit 2 [3, 2, 6, 5, 0, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_profit 1 [1, 2, 3, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible