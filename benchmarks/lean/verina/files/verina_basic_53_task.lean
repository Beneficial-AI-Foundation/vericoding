@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  sorry

@[reducible, simp]
def CalSum_postcond (N : Nat) (result: Nat) (h_precond : CalSum_precond (N)) :=
  2 * result = N * (N + 1)

theorem CalSum_spec_satisfied (N: Nat) (h_precond : CalSum_precond (N)) :
    CalSum_postcond (N) (CalSum (N) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "N": 0
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
            "N": 1
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            3
        ]
    },
    {
        "input": {
            "N": 5
        },
        "expected": 15,
        "unexpected": [
            10,
            16,
            20
        ]
    },
    {
        "input": {
            "N": 10
        },
        "expected": 55,
        "unexpected": [
            54,
            56,
            50
        ]
    },
    {
        "input": {
            "N": 20
        },
        "expected": 210,
        "unexpected": [
            200,
            220,
            205
        ]
    }
]
-/