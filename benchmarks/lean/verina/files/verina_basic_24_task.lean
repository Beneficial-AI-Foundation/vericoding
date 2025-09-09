@[reducible, simp]
def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)

-- <vc-helpers>
def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0
-- </vc-helpers>

def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  sorry

@[reducible, simp]
def firstEvenOddDifference_postcond (a : Array Int) (result: Int) (h_precond : firstEvenOddDifference_precond (a)) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))

theorem firstEvenOddDifference_spec_satisfied (a: Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    firstEvenOddDifference_postcond (a) (firstEvenOddDifference (a) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[2]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[2, 3, 4, 5]"
        },
        "expected": -1,
        "unexpected": [
            -2,
            1,
            -3
        ]
    },
    {
        "input": {
            "a": "#[1, 4, 6, 8]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4,
            5
        ]
    },
    {
        "input": {
            "a": "#[7, 2, 9, 4]"
        },
        "expected": -5,
        "unexpected": [
            -3,
            -6,
            5
        ]
    },
    {
        "input": {
            "a": "#[2, 2, 3, 3]"
        },
        "expected": -1,
        "unexpected": [
            1,
            0,
            -2
        ]
    },
    {
        "input": {
            "a": "#[1, 1, 2, 2]"
        },
        "expected": 1,
        "unexpected": [
            0,
            2,
            -1
        ]
    }
]
-/