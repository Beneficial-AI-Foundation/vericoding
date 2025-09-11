-- <vc-preamble>
@[reducible, simp]
def maxSubarraySum_precond (numbers : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxSubarraySum_postcond (numbers : List Int) (result: Int) (h_precond : maxSubarraySum_precond (numbers)) : Prop :=
  let subArraySums :=
    List.range (numbers.length + 1) |>.flatMap (fun start =>
      List.range (numbers.length - start + 1) |>.map (fun len =>
        numbers.drop start |>.take len |>.sum))
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

theorem maxSubarraySum_spec_satisfied (numbers: List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    maxSubarraySum_postcond (numbers) (maxSubarraySum (numbers) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "numbers": "[1, 2, 3, -2, 5]"
        },
        "expected": 9,
        "unexpected": [
            6,
            10,
            1
        ]
    },
    {
        "input": {
            "numbers": "[-2, -3, 4, -1, -2, 1, 5, -3]"
        },
        "expected": 7,
        "unexpected": [
            5,
            4,
            9
        ]
    },
    {
        "input": {
            "numbers": "[-1, -2, -3, -4]"
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            -10
        ]
    },
    {
        "input": {
            "numbers": "[5, -3, 2, 1, -2]"
        },
        "expected": 5,
        "unexpected": [
            3,
            6,
            4
        ]
    },
    {
        "input": {
            "numbers": "[0, 0, 0, 0]"
        },
        "expected": 0,
        "unexpected": [
            1,
            -1
        ]
    },
    {
        "input": {
            "numbers": "[]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "numbers": "[10]"
        },
        "expected": 10,
        "unexpected": [
            0,
            5
        ]
    },
    {
        "input": {
            "numbers": "[-5, 8, -3, 4, -1]"
        },
        "expected": 9,
        "unexpected": [
            8,
            3,
            0
        ]
    }
]
-/