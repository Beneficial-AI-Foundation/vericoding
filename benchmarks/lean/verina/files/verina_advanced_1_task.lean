/- 
-----Description-----
This task requires writing a Lean 4 function that finds the single number in a non-empty list of integers, where every element appears exactly twice except for one element that appears only once. The function
should return the integer that appears only once.

-----Input-----
The input is a non-empty list of integers:
- nums: A list in which each integer appears exactly twice except for one element that appears only once.

-----Output-----
The output is a single integer:
Returns the unique integer that appears exactly once in the list.
-/

@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1

-- <vc-helpers>
def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums
-- </vc-helpers>

def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  sorry

@[reducible]
def FindSingleNumber_postcond (nums : List Int) (result: Int) (h_precond : FindSingleNumber_precond (nums)) : Prop :=
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))

theorem FindSingleNumber_spec_satisfied (nums: List Int) (h_precond : FindSingleNumber_precond (nums)) :
    FindSingleNumber_postcond (nums) (FindSingleNumber (nums) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[2, 2]"
        }
    },
    {
        "input": {
            "nums": "[2, 2, 3, 3]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[2, 2, 3]"
        },
        "expected": 3,
        "unexpected": [
            2,
            1,
            4
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 2]"
        },
        "expected": 1,
        "unexpected": [
            2,
            -1
        ]
    },
    {
        "input": {
            "nums": "[3, 3, 4, 4, 1]"
        },
        "expected": 1,
        "unexpected": [
            3,
            4
        ]
    },
    {
        "input": {
            "nums": "[0, 1, 3, 1, 3, 88, 88, 100, 100]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2,
            100
        ]
    },
    {
        "input": {
            "nums": "[-1, -1, 7, 9, 7]"
        },
        "expected": 9,
        "unexpected": [
            -1,
            7,
            10
        ]
    }
]
-/