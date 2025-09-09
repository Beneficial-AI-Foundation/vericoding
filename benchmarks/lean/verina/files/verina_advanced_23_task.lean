@[reducible]
def isPowerOfTwo_precond (n : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def isPowerOfTwo (n : Int) (h_precond : isPowerOfTwo_precond (n)) : Bool :=
  sorry

def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1
  | n+1 => base * pow base n
@[reducible]
def isPowerOfTwo_postcond (n : Int) (result: Bool) (h_precond : isPowerOfTwo_precond (n)) : Prop :=
  if result then ∃ (x : Nat), (pow 2 x = n) ∧ (n > 0)
  else ¬ (∃ (x : Nat), (pow 2 x = n) ∧ (n > 0))

theorem isPowerOfTwo_spec_satisfied (n: Int) (h_precond : isPowerOfTwo_precond (n)) :
    isPowerOfTwo_postcond (n) (isPowerOfTwo (n) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
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
            "n": 16
        },
        "expected": true,
        "unexpected": [
            false
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
            "n": 0
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": -2
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "n": 8
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "n": 10
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/