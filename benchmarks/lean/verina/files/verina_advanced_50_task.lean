@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList

-- <vc-helpers>
-- </vc-helpers>

def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Array Nat :=
  sorry

@[reducible]
def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)

theorem mergeSorted_spec_satisfied (a1: Array Nat) (a2: Array Nat) :
    mergeSorted_postcond (a1) (a2) (mergeSorted (a1) (a2)) := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "a1": "#[3, 2, 1]",
            "a2": "#[6, 5, 4]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a1": "#[1, 3, 5]",
            "a2": "#[2, 4, 6]"
        },
        "expected": "#[1, 2, 3, 4, 5, 6]",
        "unexpected": [
            "#[1, 3, 5, 2, 4, 6]",
            "#[2, 1, 3, 4, 5, 6]"
        ]
    },
    {
        "input": {
            "a1": "#[]",
            "a2": "#[1, 2, 3]"
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[]",
            "#[3, 2, 1]"
        ]
    },
    {
        "input": {
            "a1": "#[1, 2, 3]",
            "a2": "#[]"
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[]",
            "#[3, 2, 1]"
        ]
    },
    {
        "input": {
            "a1": "#[]",
            "a2": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]"
        ]
    },
    {
        "input": {
            "a1": "#[1, 1, 2]",
            "a2": "#[1, 2, 2]"
        },
        "expected": "#[1, 1, 1, 2, 2, 2]",
        "unexpected": [
            "#[1, 1, 2, 1, 2, 2]",
            "#[1, 2]"
        ]
    },
    {
        "input": {
            "a1": "#[10, 20, 30]",
            "a2": "#[5, 15, 25]"
        },
        "expected": "#[5, 10, 15, 20, 25, 30]",
        "unexpected": [
            "#[10, 20, 30, 5, 15, 25]"
        ]
    },
    {
        "input": {
            "a1": "#[1, 3, 5, 7, 9]",
            "a2": "#[2, 4, 6, 8, 10]"
        },
        "expected": "#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]",
        "unexpected": [
            "#[1, 3, 5, 7, 9, 2, 4, 6, 8, 10]"
        ]
    },
    {
        "input": {
            "a1": "#[5, 5, 5]",
            "a2": "#[5, 5, 5]"
        },
        "expected": "#[5, 5, 5, 5, 5, 5]",
        "unexpected": [
            "#[5, 5, 5]"
        ]
    }
]
-/