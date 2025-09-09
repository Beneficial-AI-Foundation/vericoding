@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  List.Pairwise (· < ·) xs

-- <vc-helpers>
-- </vc-helpers>

def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  sorry

@[reducible]
def searchInsert_postcond (xs : List Int) (target : Int) (result: Nat) (h_precond : searchInsert_precond (xs) (target)) : Prop :=
  let allBeforeLess := (List.range result).all (fun i => xs[i]! < target)
  let inBounds := result ≤ xs.length
  let insertedCorrectly :=
    result < xs.length → target ≤ xs[result]!
  inBounds ∧ allBeforeLess ∧ insertedCorrectly

theorem searchInsert_spec_satisfied (xs: List Int) (target: Int) (h_precond : searchInsert_precond (xs) (target)) :
    searchInsert_postcond (xs) (target) (searchInsert (xs) (target) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "xs": "[2, 1]",
            "target": 5
        }
    },
    {
        "input": {
            "xs": "[1, 1]",
            "target": 2
        }
    }
]
-- Tests
[
    {
        "input": {
            "xs": "[1, 3, 5, 6]",
            "target": 5
        },
        "expected": 2,
        "unexpected": [
            0,
            1,
            3,
            4
        ]
    },
    {
        "input": {
            "xs": "[1, 3, 5, 6]",
            "target": 2
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            3
        ]
    },
    {
        "input": {
            "xs": "[1, 3, 5, 6]",
            "target": 7
        },
        "expected": 4,
        "unexpected": [
            2,
            3
        ]
    },
    {
        "input": {
            "xs": "[1, 3, 5, 6]",
            "target": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "xs": "[]",
            "target": 3
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "xs": "[10]",
            "target": 5
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "xs": "[10]",
            "target": 15
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    }
]
-/