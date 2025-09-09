@[reducible]
def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  sorry

@[reducible]
def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat) (h_precond : removeElement_precond (lst) (target)): Prop :=
  -- 1. All elements equal to target are removed from the result.
  -- 2. All other elements are preserved in order.
  -- 3. No new elements are added.

  -- Helper predicate: result contains exactly the elements of lst that are not equal to target, in order
  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length

theorem removeElement_spec_satisfied (lst: List Nat) (target: Nat) (h_precond : removeElement_precond (lst) (target)):
    removeElement_postcond (lst) (target) (removeElement (lst) (target) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "lst": "[1, 2, 3, 2, 4]",
            "target": 2
        },
        "expected": "[1, 3, 4]",
        "unexpected": [
            "[1, 2, 3, 4]",
            "[1, 2, 3]",
            "[1, 4]"
        ]
    },
    {
        "input": {
            "lst": "[5, 5, 5, 5]",
            "target": 5
        },
        "expected": "[]",
        "unexpected": [
            "[5]",
            "[0]",
            "[5, 5]"
        ]
    },
    {
        "input": {
            "lst": "[7, 8, 9]",
            "target": 4
        },
        "expected": "[7, 8, 9]",
        "unexpected": [
            "[]",
            "[7, 8]",
            "[8, 9]"
        ]
    },
    {
        "input": {
            "lst": "[]",
            "target": 3
        },
        "expected": "[]",
        "unexpected": [
            "[3]",
            "[0]",
            "[1, 2, 3]"
        ]
    },
    {
        "input": {
            "lst": "[0, 1, 0, 2, 0]",
            "target": 0
        },
        "expected": "[1, 2]",
        "unexpected": [
            "[0, 1, 2]",
            "[1]",
            "[1, 0, 2]"
        ]
    }
]
-/