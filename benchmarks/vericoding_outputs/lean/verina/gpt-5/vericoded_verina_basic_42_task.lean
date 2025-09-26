import Mathlib
-- <vc-preamble>
@[reducible, simp]
def countDigits_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def isDigit (c : Char) : Bool := c.isDigit
-- </vc-helpers>

-- <vc-definitions>
def countDigits (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  (List.filter isDigit s.toList).length
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countDigits_postcond (s : String) (result: Nat) (h_precond : countDigits_precond (s)) :=
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0

theorem countDigits_spec_satisfied (s: String) (h_precond : countDigits_precond (s)) :
    countDigits_postcond (s) (countDigits (s) h_precond) h_precond := by
  dsimp [countDigits_postcond]
  constructor
  · simp [countDigits]
  · simp [countDigits]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "123abc456"
        },
        "expected": 6,
        "unexpected": [
            5,
            7,
            0
        ]
    },
    {
        "input": {
            "s": "no digits here!"
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            3
        ]
    },
    {
        "input": {
            "s": "1234567890"
        },
        "expected": 10,
        "unexpected": [
            9,
            11,
            0
        ]
    },
    {
        "input": {
            "s": ""
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            10
        ]
    },
    {
        "input": {
            "s": "a1b2c3"
        },
        "expected": 3,
        "unexpected": [
            2,
            4,
            5
        ]
    },
    {
        "input": {
            "s": "0"
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            10
        ]
    },
    {
        "input": {
            "s": "abc"
        },
        "expected": 0,
        "unexpected": [
            1,
            8,
            9
        ]
    }
]
-/