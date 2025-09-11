-- <vc-preamble>
@[reducible, simp]
def majorityElement_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  let n := nums.length
  (List.count result nums > n / 2) ∧
  nums.all (fun x => x = result ∨ List.count x nums ≤ n / 2)

theorem majorityElement_spec_satisfied (nums: List Int) (h_precond : majorityElement_precond (nums)) :
    majorityElement_postcond (nums) (majorityElement (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "nums": "[3, 2, 3]"
        },
        "expected": 3,
        "unexpected": [
            2
        ]
    },
    {
        "input": {
            "nums": "[2, 2, 1, 1, 1, 2, 2]"
        },
        "expected": 2,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "nums": "[1]"
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    },
    {
        "input": {
            "nums": "[4, 4, 4, 4, 4, 2, 2, 3, 3]"
        },
        "expected": 4,
        "unexpected": [
            2,
            3
        ]
    },
    {
        "input": {
            "nums": "[9, 8, 9, 9, 7, 9, 6, 9, 9]"
        },
        "expected": 9,
        "unexpected": [
            6,
            7,
            8
        ]
    },
    {
        "input": {
            "nums": "[0, 0, 0, 0, 1]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "nums": "[100000, 100000, 100000, 100000, -100000]"
        },
        "expected": 100000,
        "unexpected": [
            -100000
        ]
    },
    {
        "input": {
            "nums": "[-1, -1, -1, -1, 0, 1, 2]"
        },
        "expected": -1,
        "unexpected": [
            0,
            1,
            2
        ]
    },
    {
        "input": {
            "nums": "[5, 5, 5, 5, 5, 5, 5]"
        },
        "expected": 5,
        "unexpected": [
            0
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 3, 3, 3, 3, 3]"
        },
        "expected": 3,
        "unexpected": [
            1,
            2
        ]
    }
]
-/