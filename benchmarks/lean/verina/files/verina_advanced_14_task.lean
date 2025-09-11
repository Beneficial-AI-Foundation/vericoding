-- <vc-preamble>
@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)

theorem ifPowerOfFour_spec_satisfied (n: Nat) (h_precond : ifPowerOfFour_precond (n)) :
    ifPowerOfFour_postcond (n) (ifPowerOfFour (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "n": 0
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 1
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 2
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 3
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 4
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 8
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 16
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 64
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 95
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 100
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 256
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 520
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 1024
        },
        "expected": true,
        "unexpected": [
            false
        ]
    }
]
-/