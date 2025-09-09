@[reducible]
def nextGreaterElement_precond (nums1 : List Int) (nums2 : List Int) : Prop :=
  List.Nodup nums1 ∧
  List.Nodup nums2 ∧
  nums1.all (fun x => x ∈ nums2)

-- <vc-helpers>
-- </vc-helpers>

def nextGreaterElement (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : List Int :=
  sorry

@[reducible]
def nextGreaterElement_postcond (nums1 : List Int) (nums2 : List Int) (result: List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : Prop :=
  result.length = nums1.length ∧

  (List.range nums1.length |>.all (fun i =>
    let val := nums1[i]!
    let resultVal := result[i]!

    let j := nums2.findIdx? (fun x => x == val)
    match j with
    | none => false
    | some idx =>
      let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k =>
        let pos := idx + k + 1
        nums2[pos]! > val
      )

      match nextGreater with
      | none => resultVal = -1
      | some offset => resultVal = nums2[idx + offset + 1]!
  )) ∧
  (result.all (fun val =>
    val = -1 ∨ val ∈ nums2
  ))

theorem nextGreaterElement_spec_satisfied (nums1: List Int) (nums2: List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    nextGreaterElement_postcond (nums1) (nums2) (nextGreaterElement (nums1) (nums2) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums1": "[1, 3]",
            "nums2": "[1, 2]"
        }
    },
    {
        "input": {
            "nums1": "[1, 1]",
            "nums2": "[1, 2]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums1": "[4, 1, 2]",
            "nums2": "[1, 3, 4, 2]"
        },
        "expected": "[-1, 3, -1]",
        "unexpected": [
            "[3, -1, 3]"
        ]
    },
    {
        "input": {
            "nums1": "[2, 4]",
            "nums2": "[1, 2, 3, 4]"
        },
        "expected": "[3, -1]",
        "unexpected": [
            "[-1, 3]"
        ]
    },
    {
        "input": {
            "nums1": "[1]",
            "nums2": "[1, 2]"
        },
        "expected": "[2]",
        "unexpected": [
            "[-1]"
        ]
    },
    {
        "input": {
            "nums1": "[5]",
            "nums2": "[5, 4, 3, 2, 1]"
        },
        "expected": "[-1]",
        "unexpected": [
            "[4]"
        ]
    },
    {
        "input": {
            "nums1": "[1, 3, 5, 2, 4]",
            "nums2": "[6, 5, 4, 3, 2, 1]"
        },
        "expected": "[-1, -1, -1, -1, -1]",
        "unexpected": [
            "[6, 5, 6, 3, 6]"
        ]
    },
    {
        "input": {
            "nums1": "[1, 2, 3]",
            "nums2": "[3, 2, 1, 4]"
        },
        "expected": "[4, 4, 4]",
        "unexpected": [
            "[-1, -1, -1]"
        ]
    },
    {
        "input": {
            "nums1": "[4, 3, 2, 1]",
            "nums2": "[4, 3, 2, 1]"
        },
        "expected": "[-1, -1, -1, -1]",
        "unexpected": [
            "[3, 2, 1, -1]"
        ]
    }
]
-/