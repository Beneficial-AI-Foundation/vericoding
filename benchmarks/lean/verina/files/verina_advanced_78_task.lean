@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  let pairwiseSum := List.range nums.length |>.flatMap (fun i =>
    nums.drop (i + 1) |>.map (fun y => nums[i]! + y))
  nums.length > 1 ∧ pairwiseSum.count target = 1

-- <vc-helpers>
def findComplement (nums : List Int) (target : Int) (i : Nat) (x : Int) : Option Nat :=
  let rec aux (nums : List Int) (j : Nat) : Option Nat :=
    match nums with
    | []      => none
    | y :: ys => if x + y = target then some (i + j + 1) else aux ys (j + 1)
  aux nums 0

def twoSumAux (nums : List Int) (target : Int) (i : Nat) : Prod Nat Nat :=
  match nums with
  | []      => panic! "No solution exists"
  | x :: xs =>
    match findComplement xs target i x with
    | some j => (i, j)
    | none   => twoSumAux xs target (i + 1)
-- </vc-helpers>

def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Prod Nat Nat :=
  sorry

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Prod Nat Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  let i := result.fst;
  let j := result.snd;
  (i < j) ∧
  (i < nums.length) ∧ (j < nums.length) ∧
  (nums[i]!) + (nums[j]!) = target

theorem twoSum_spec_satisfied (nums: List Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[1, 2]",
            "target": 0
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[2, 7, 11, 15]",
            "target": 9
        },
        "expected": "(0, 1)",
        "unexpected": [
            "(2, 3)"
        ]
    },
    {
        "input": {
            "nums": "[3, 2, 4]",
            "target": 6
        },
        "expected": "(1, 2)",
        "unexpected": [
            "(0, 2)"
        ]
    },
    {
        "input": {
            "nums": "[3, 3]",
            "target": 6
        },
        "expected": "(0, 1)",
        "unexpected": [
            "(1, 0)"
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 3, 4]",
            "target": 7
        },
        "expected": "(2, 3)",
        "unexpected": [
            "(0, 1)"
        ]
    },
    {
        "input": {
            "nums": "[0, 4, 3, 0]",
            "target": 0
        },
        "expected": "(0, 3)",
        "unexpected": [
            "(1, 2)"
        ]
    }
]
-/