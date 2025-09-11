-- <vc-preamble>
def lastStoneWeightII (stones : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem lastStoneWeight_nonNegative (stones : List Nat) :
  lastStoneWeightII stones ≥ 0 :=
sorry

theorem lastStoneWeight_upperBound (stones : List Nat) :
  lastStoneWeightII stones ≤ sum stones :=
sorry

theorem lastStoneWeight_identical_pairs (stones : List Nat) :
  stones.length = 2 → stones[0]! = stones[1]! → lastStoneWeightII stones = 0 :=
sorry

theorem lastStoneWeight_single_stone (stones : List Nat) (x : Nat) :
  stones = [x] → lastStoneWeightII stones = x :=
sorry

theorem lastStoneWeight_identical_values (stones : List Nat) (x : Nat) :
  (∀ i, i < stones.length → stones[i]! = x) → lastStoneWeightII stones ≤ x :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval lastStoneWeightII [2, 7, 4, 1, 8, 1]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval lastStoneWeightII [1, 1, 1]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval lastStoneWeightII [2, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded