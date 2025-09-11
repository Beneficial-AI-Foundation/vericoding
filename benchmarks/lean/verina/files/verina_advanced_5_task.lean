-- <vc-preamble>
@[reducible]
def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])
-- </vc-preamble>

-- <vc-helpers>
def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds
-- </vc-helpers>

-- <vc-definitions>
def addTwoNumbers (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : Prop :=
  listToNat result = listToNat l1 + listToNat l2 ∧
  (∀ d ∈ result, d < 10) ∧
  -- No leading zeros unless the result is zero
  (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0]))

theorem addTwoNumbers_spec_satisfied (l1: List Nat) (l2: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    addTwoNumbers_postcond (l1) (l2) (addTwoNumbers (l1) (l2) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "l1": "[]",
            "l2": "[]"
        }
    },
    {
        "input": {
            "l1": "[0, 0]",
            "l2": "[0, 0]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "l1": "[2,4,3]",
            "l2": "[5,6,4]"
        },
        "expected": "[7,0,8]",
        "unexpected": [
            "[2,4,3]",
            "[0]"
        ]
    },
    {
        "input": {
            "l1": "[0]",
            "l2": "[0]"
        },
        "expected": "[0]",
        "unexpected": [
            "[0,0]"
        ]
    },
    {
        "input": {
            "l1": "[9,9,9,9,9,9,9]",
            "l2": "[9,9,9,9]"
        },
        "expected": "[8,9,9,9,0,0,0,1]",
        "unexpected": [
            "[9,9,9,9,9,9,9,9]"
        ]
    },
    {
        "input": {
            "l1": "[1,2,3]",
            "l2": "[4,5]"
        },
        "expected": "[5,7,3]",
        "unexpected": [
            "[5,7]",
            "[5,7,4]"
        ]
    }
]
-/