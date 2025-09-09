@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True

-- <vc-helpers>
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- </vc-helpers>

def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  sorry

@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)

theorem findEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    findEvenNumbers_postcond (arr) (findEvenNumbers (arr) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "arr": "#[1, 2, 3, 4, 5, 6]"
        },
        "expected": "#[2, 4, 6]",
        "unexpected": [
            "#[1, 2, 3]",
            "#[2, 3, 4, 6]"
        ]
    },
    {
        "input": {
            "arr": "#[7, 8, 10, 13, 14]"
        },
        "expected": "#[8, 10, 14]",
        "unexpected": [
            "#[7, 8, 10]",
            "#[8, 14]"
        ]
    },
    {
        "input": {
            "arr": "#[1, 3, 5, 7]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]",
            "#[1, 3]"
        ]
    },
    {
        "input": {
            "arr": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[0]",
            "#[1]"
        ]
    },
    {
        "input": {
            "arr": "#[0, -2, -3, -4, 5]"
        },
        "expected": "#[0, -2, -4]",
        "unexpected": [
            "#[0, -3, -4]",
            "#[-2, -4]"
        ]
    }
]
-/