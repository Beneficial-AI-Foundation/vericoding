/- 
-----Description-----
This task involves determining how many numbers within an array are less than a specified threshold. The problem is focused on identifying and counting such numbers based purely on their value in relation to the threshold.

-----Input-----
The input consists of:
• numbers: An array of integers (which may be empty or non-empty).
• threshold: An integer that serves as the comparison threshold.

-----Output-----
The output is a natural number (Nat) representing the count of elements in the array that are less than the given threshold.

-----Note-----
There are no additional preconditions; the function should work correctly for any array of integers and any integer threshold.
-/

@[reducible, simp]
def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  True

-- <vc-helpers>
def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0
-- </vc-helpers>

def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0

theorem CountLessThan_spec_satisfied (numbers: Array Int) (threshold: Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    CountLessThan_postcond (numbers) (threshold) (CountLessThan (numbers) (threshold) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

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
