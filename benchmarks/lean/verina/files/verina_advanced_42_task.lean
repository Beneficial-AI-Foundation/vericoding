-- <vc-preamble>
@[reducible, simp]
def maxProfit_precond (prices : List Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def updateMinAndProfit (price : Nat) (minSoFar : Nat) (maxProfit : Nat) : (Nat × Nat) :=
  let newMin := Nat.min minSoFar price
  let profit := if price > minSoFar then price - minSoFar else 0
  let newMaxProfit := Nat.max maxProfit profit
  (newMin, newMaxProfit)

def maxProfitAux (prices : List Nat) (minSoFar : Nat) (maxProfit : Nat) : Nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let (newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit
    maxProfitAux ps newMin newProfit
-- </vc-helpers>

-- <vc-definitions>
def maxProfit (prices : List Nat) (h_precond : maxProfit_precond (prices)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxProfit_postcond (prices : List Nat) (result: Nat) (h_precond : maxProfit_precond (prices)) : Prop :=
  (result = 0 ∧ prices = []) ∨
  (
    -- All valid transactions have profit ≤ result (using pairwise)
    List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ result) prices.zipIdx ∧

    -- There exists a transaction with profit = result (using any)
    prices.zipIdx.any (fun ⟨pi, i⟩ =>
      prices.zipIdx.any (fun ⟨pj, j⟩ =>
        i < j ∧ pj - pi = result))
  )

theorem maxProfit_spec_satisfied (prices: List Nat) (h_precond : maxProfit_precond (prices)) :
    maxProfit_postcond (prices) (maxProfit (prices) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "prices": "[7, 1, 5, 3, 6, 4]"
        },
        "expected": 5,
        "unexpected": [
            4,
            6
        ]
    },
    {
        "input": {
            "prices": "[7, 6, 4, 3, 1]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "prices": "[2, 4, 1]"
        },
        "expected": 2,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "prices": "[1, 2]"
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    },
    {
        "input": {
            "prices": "[]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    }
]
-/