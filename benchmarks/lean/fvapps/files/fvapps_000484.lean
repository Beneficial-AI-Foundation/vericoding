-- <vc-preamble>
def sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lastStoneWeightII (stones : List Nat) : Nat :=
  sorry
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
-- </vc-theorems>