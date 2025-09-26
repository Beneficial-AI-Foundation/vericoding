import Mathlib
-- <vc-preamble>
@[reducible]
def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- No helper functions needed
-- </vc-helpers>

-- <vc-definitions>
def semiOrderedPermutation (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
  let n := nums.length
  let pos1 := nums.idxOf 1
  let posn := nums.idxOf (Int.ofNat n)
  if pos1 > posn then
    pos1 + n - posn - 2
  else
    pos1 + n - posn - 1
-- </vc-definitions>

-- <vc-theorems>
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
  unfold semiOrderedPermutation_postcond semiOrderedPermutation
  simp only
  split_ifs <;> ring
-- </vc-theorems>

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