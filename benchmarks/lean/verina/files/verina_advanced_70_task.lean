/- 
-----Description---
This task requires writing a Lean 4 method that's goal is to determine the minimum number of adjacent swaps needed to make the array semi-ordered. You may repeatedly swap 2 adjacent elements in the array. A permutation is called semi-ordered if the first number equals 1 and the last number equals n.

-----Input-----

The input consists of:
- nums: A list of integeris.

----Output-----

The output is an integer.
-/

@[reducible]
def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def semiOrderedPermutation (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible]
def semiOrderedPermutation_postcond (nums : List Int) (result: Int) (h_precond : semiOrderedPermutation_precond (nums)) : Prop :=
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n = result + 2 + posn
  else
    pos1 + n = result + 1 + posn

theorem semiOrderedPermutation_spec_satisfied (nums: List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    semiOrderedPermutation_postcond (nums) (semiOrderedPermutation (nums) h_precond) h_precond := by
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
            "nums": "[2, 1, 4, 3]"
        },
        "expected": 2,
        "unexpected": [
            0,
            1,
            3
        ]
    },
    {
        "input": {
            "nums": "[2, 4, 1, 3]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4
        ]
    },
    {
        "input": {
            "nums": "[1, 3, 4, 2, 5]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "nums": "[3, 1, 2]"
        },
        "expected": 2,
        "unexpected": [
            0,
            1
        ]
    },
    {
        "input": {
            "nums": "[2, 3, 1, 5, 4]"
        },
        "expected": 3,
        "unexpected": [
            4,
            5
        ]
    }
]
-/
