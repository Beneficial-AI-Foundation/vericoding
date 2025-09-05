/- 
-----Description-----
This task requires writing a Lean 4 method that finds the **majority element** in a list of integers. A majority element is defined as an element that appears **strictly more than half** the number of times in the list.

If such an element exists, the method should return that element. Otherwise, it should return `-1`. The implementation must ensure that the result is either the majority element (if one exists) or `-1` (when no such element appears more than ⌊n/2⌋ times).

-----Input-----
The input consists of a list of integers:
- lst: A list of integers, which may include duplicates and negative numbers. The list may also be empty.

-----Output-----
The output is a single integer:
- If a majority element exists in the input list, return that element.
- If no majority element exists, return `-1`.
-/

@[reducible, simp]
def findMajorityElement_precond (lst : List Int) : Prop :=
  True

-- <vc-helpers>
def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0
-- </vc-helpers>

def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

theorem findMajorityElement_spec_satisfied (lst: List Int) (h_precond : findMajorityElement_precond (lst)) :
    findMajorityElement_postcond (lst) (findMajorityElement (lst) h_precond) h_precond := by
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
            "lst": "[1, 2, 1, 1]"
        },
        "expected": 1,
        "unexpected": [
            2,
            -1
        ]
    },
    {
        "input": {
            "lst": "[1, 2, 3, 4]"
        },
        "expected": -1,
        "unexpected": [
            1,
            2,
            3,
            4
        ]
    },
    {
        "input": {
            "lst": "[2, 2, 2, 2, 3, 3]"
        },
        "expected": 2,
        "unexpected": [
            3,
            -1
        ]
    },
    {
        "input": {
            "lst": "[]"
        },
        "expected": -1,
        "unexpected": [
            0,
            1
        ]
    },
    {
        "input": {
            "lst": "[5, 5, 5, 5, 5, 5]"
        },
        "expected": 5,
        "unexpected": [
            0,
            -1
        ]
    },
    {
        "input": {
            "lst": "[-1, -1, -1, 2, 2]"
        },
        "expected": -1,
        "unexpected": [
            2
        ]
    },
    {
        "input": {
            "lst": "[-3, -3, -3, -3, 1]"
        },
        "expected": -3,
        "unexpected": [
            1,
            -1
        ]
    }
]
-/
