/- 
-----Description-----
This task requires writing a Lean 4 method that determines whether a list of integers follows a peak-valley pattern.

A list follows this pattern if:
A. It strictly increases at first,
B. Then strictly decreases,
C. Both parts are non-empty.

Examples:
- [1, 3, 5, 4, 2] -> true
- [1, 2, 3] -> false
- [5, 4, 3] -> false
- [1, 2, 2, 1] -> false

-----Input-----
The input consists of a list of integers:

-----Output-----
The output is an integer:
Returns true if the list has a peak-valley structure, false otherwise.
-/

@[reducible, simp]
def isPeakValley_precond (lst : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def isPeakValley (lst : List Int) (h_precond : isPeakValley_precond (lst)) : Bool :=
  sorry

@[reducible, simp]
def isPeakValley_postcond (lst : List Int) (result: Bool) (h_precond : isPeakValley_precond (lst)) : Prop :=
  let len := lst.length
  let validPeaks :=
    List.range len |>.filter (fun p =>
      1 ≤ p ∧ p < len - 1 ∧

      -- check strictly increasing before peak
      (List.range p).all (fun i =>
        lst[i]! < lst[i + 1]!
      ) ∧

      -- check strictly decreasing after peak
      (List.range (len - 1 - p)).all (fun i =>
        lst[p + i]! > lst[p + i + 1]!
      )
    )
  (validPeaks != [] → result) ∧
  (validPeaks.length = 0 → ¬ result)

theorem isPeakValley_spec_satisfied (lst: List Int) (h_precond : isPeakValley_precond (lst)) :
    isPeakValley_postcond (lst) (isPeakValley (lst) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "lst": "[1, 3, 5, 2, 1]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "lst": "[1, 2, 3, 4, 5]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "lst": "[]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "lst": "[1]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "lst": "[1, 1, 1, 1, 1]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "lst": "[1, 10, 100, 1]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    }
]
-/