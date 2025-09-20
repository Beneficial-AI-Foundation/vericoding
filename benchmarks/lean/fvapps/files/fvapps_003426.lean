-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def looseChange (coins: List Nat) (amount: Nat) : Int :=
  sorry

def listMin (l: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem looseChange_result_bound (coins: List Nat) (amount: Nat) :
  coins.length > 0 → let result := looseChange coins amount
  result ≥ -1 := by
sorry

theorem looseChange_zero (coins: List Nat) :
  coins.length > 0 → looseChange coins 0 = 0 := by
sorry

theorem looseChange_small_amount (coins: List Nat) (amount: Nat) :
  coins.length > 0 →
  amount > 0 →
  amount < listMin coins →
  looseChange coins amount = -1 := by
sorry

theorem looseChange_bounded_by_amount (coins: List Nat) (amount: Nat) :
  coins.length > 0 →
  looseChange coins amount ≠ -1 →
  looseChange coins amount ≤ amount := by
sorry

theorem looseChange_optimal (coins: List Nat) (amount: Nat) :
  coins.length > 0 →
  let result := looseChange coins amount
  result ≠ -1 →
  ∀ (c : Nat),
  c ∈ coins →
  ¬∃ (n : Nat), n > result ∧ n * c = amount := by
sorry
-- </vc-theorems>