import Mathlib
-- <vc-preamble>
@[reducible, simp]
def sumOfDigits_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n)))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0

theorem sumOfDigits_spec_satisfied (n: Nat) (h_precond : sumOfDigits_precond (n)) :
    sumOfDigits_postcond (n) (sumOfDigits (n) h_precond) h_precond := by
  unfold sumOfDigits_postcond sumOfDigits
  constructor <;> simp
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 12345
        },
        "expected": 15,
        "unexpected": [
            12,
            16,
            14
        ]
    },
    {
        "input": {
            "n": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            10,
            5
        ]
    },
    {
        "input": {
            "n": 987654321
        },
        "expected": 45,
        "unexpected": [
            44,
            46,
            50
        ]
    },
    {
        "input": {
            "n": 11111
        },
        "expected": 5,
        "unexpected": [
            6,
            4,
            7
        ]
    },
    {
        "input": {
            "n": 1001
        },
        "expected": 2,
        "unexpected": [
            1,
            3,
            11
        ]
    },
    {
        "input": {
            "n": 9999
        },
        "expected": 36,
        "unexpected": [
            35,
            37,
            34
        ]
    }
]
-/