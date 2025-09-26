import Mathlib
-- <vc-preamble>
@[reducible, simp]
def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0

@[simp]
theorem countLessThan_spec (numbers : Array Int) (threshold : Int) :
    countLessThan numbers threshold =
      numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 := rfl
-- </vc-helpers>

-- <vc-definitions>
def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0

theorem CountLessThan_spec_satisfied (numbers: Array Int) (threshold: Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    CountLessThan_postcond (numbers) (threshold) (CountLessThan (numbers) (threshold) h_precond) h_precond := by
  simpa [CountLessThan_postcond, CountLessThan]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "numbers": "#[1, 2, 3, 4, 5]",
            "threshold": 3
        },
        "expected": "2",
        "unexpected": [
            "3",
            "1",
            "0"
        ]
    },
    {
        "input": {
            "numbers": "#[]",
            "threshold": 10
        },
        "expected": "0",
        "unexpected": [
            "1",
            "2",
            "3"
        ]
    },
    {
        "input": {
            "numbers": "#[-1, 0, 1]",
            "threshold": 0
        },
        "expected": "1",
        "unexpected": [
            "0",
            "2",
            "3"
        ]
    },
    {
        "input": {
            "numbers": "#[5, 6, 7, 2, 1]",
            "threshold": 5
        },
        "expected": "2",
        "unexpected": [
            "3",
            "4",
            "1"
        ]
    },
    {
        "input": {
            "numbers": "#[3, 3, 3, 3]",
            "threshold": 3
        },
        "expected": "0",
        "unexpected": [
            "1",
            "2",
            "3"
        ]
    }
]
-/