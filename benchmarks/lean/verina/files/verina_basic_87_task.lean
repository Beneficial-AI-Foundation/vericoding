-- <vc-preamble>
@[reducible, simp]
def SelectionSort_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList

theorem SelectionSort_spec_satisfied (a: Array Int) (h_precond : SelectionSort_precond (a)) :
    SelectionSort_postcond (a) (SelectionSort (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[3, 1, 2]"
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[3, 1, 2]",
            "#[2, 3, 1]"
        ]
    },
    {
        "input": {
            "a": "#[0]"
        },
        "expected": "#[0]",
        "unexpected": [
            "#[0, 0]",
            "#[1]"
        ]
    },
    {
        "input": {
            "a": "#[5, 4, 3, 2, 1]"
        },
        "expected": "#[1, 2, 3, 4, 5]",
        "unexpected": [
            "#[5, 4, 3, 2, 1]",
            "#[1, 5, 4, 3, 2]",
            "#[1, 2, 4, 3, 5]"
        ]
    },
    {
        "input": {
            "a": "#[2, 2, 1, 4]"
        },
        "expected": "#[1, 2, 2, 4]",
        "unexpected": [
            "#[2, 1, 2, 4]",
            "#[1, 2, 4, 2]"
        ]
    },
    {
        "input": {
            "a": "#[10, -5, 0, 3]"
        },
        "expected": "#[-5, 0, 3, 10]",
        "unexpected": [
            "#[10, -5, 3, 0]",
            "#[0, -5, 3, 10]",
            "#[3, -5, 10, 0]"
        ]
    }
]
-/