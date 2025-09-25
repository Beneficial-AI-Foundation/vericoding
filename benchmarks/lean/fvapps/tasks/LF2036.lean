-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_lost_milk (n: Nat) (cows: List Nat) : Nat :=
sorry

def count_facing (cows: List Nat) (dir: Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_lost_milk_non_negative (n: Nat) (cows: List Nat) :
  min_lost_milk n cows ≥ 0 :=
sorry

theorem min_lost_milk_length (n: Nat) (cows: List Nat) :
  cows.length = n → True :=
sorry
-- </vc-theorems>