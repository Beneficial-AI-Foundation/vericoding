-- <vc-preamble>
@[reducible, simp]
def task_code_precond (sequence : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def task_code (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def task_code_postcond (sequence : List Int) (result: Int) (h_precond : task_code_precond (sequence)) : Prop :=
  let subArrays :=
    List.range (sequence.length + 1) |>.flatMap (fun start =>
      List.range (sequence.length - start + 1) |>.map (fun len =>
        sequence.drop start |>.take len))
  let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum)
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

theorem task_code_spec_satisfied (sequence: List Int) (h_precond : task_code_precond (sequence)) :
    task_code_postcond (sequence) (task_code (sequence) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "sequence": "[10, -4, 3, 1, 5, 6, -35, 12, 21, -1]"
        },
        "expected": 33,
        "unexpected": [
            32,
            34,
            0
        ]
    },
    {
        "input": {
            "sequence": "[2, 1, -4, 3, 4, -4, 6, 5, -5, 1]"
        },
        "expected": 14,
        "unexpected": [
            13,
            15,
            0
        ]
    },
    {
        "input": {
            "sequence": "[-1, -2, -3, -4, -5]"
        },
        "expected": -1,
        "unexpected": [
            -2,
            0,
            1
        ]
    },
    {
        "input": {
            "sequence": "[7]"
        },
        "expected": 7,
        "unexpected": [
            0,
            1,
            -7
        ]
    },
    {
        "input": {
            "sequence": "[1, 2, 3, 4, 5]"
        },
        "expected": 15,
        "unexpected": [
            14,
            16,
            0
        ]
    }
]
-/