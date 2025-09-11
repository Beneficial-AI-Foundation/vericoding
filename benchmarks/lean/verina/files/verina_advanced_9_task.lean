-- <vc-preamble>
@[reducible]
def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  d > 0
-- </vc-preamble>

-- <vc-helpers>
def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0

def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0
-- </vc-helpers>

-- <vc-definitions>
def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def countSumDivisibleBy_postcond (n : Nat) (d : Nat) (result: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Prop :=
  (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n))) - result = 0 ∧
  result ≤ (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)))

theorem countSumDivisibleBy_spec_satisfied (n: Nat) (d: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    countSumDivisibleBy_postcond (n) (d) (countSumDivisibleBy (n) (d) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "n": 1,
            "d": 0
        }
    }
]
-- Tests
[
    {
        "input": {
            "n": 0,
            "d": 2
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "n": 1,
            "d": 2
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    },
    {
        "input": {
            "n": 10,
            "d": 3
        },
        "expected": 4,
        "unexpected": [
            3,
            5
        ]
    },
    {
        "input": {
            "n": 12,
            "d": 2
        },
        "expected": 6,
        "unexpected": [
            3,
            5
        ]
    },
    {
        "input": {
            "n": 20,
            "d": 5
        },
        "expected": 4,
        "unexpected": [
            0,
            10
        ]
    }
]
-/