-- <vc-preamble>
@[reducible, simp]
def BubbleSort_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BubbleSort (a : Array Int) (h_precond : BubbleSort_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def BubbleSort_postcond (a : Array Int) (result: Array Int) (h_precond : BubbleSort_precond (a)) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm result.toList a.toList

theorem BubbleSort_spec_satisfied (a: Array Int) (h_precond : BubbleSort_precond (a)) :
    BubbleSort_postcond (a) (BubbleSort (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[5, 4, 3, 2, 1]"
        },
        "expected": "#[1, 2, 3, 4, 5]",
        "unexpected": [
            "#[5, 4, 3, 2, 1]",
            "#[2, 3, 1, 4, 5]"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": "#[1, 2, 3, 4, 5]",
        "unexpected": [
            "#[5, 4, 3, 2, 1]",
            "#[1, 3, 2, 4, 5]"
        ]
    },
    {
        "input": {
            "a": "#[3, 1, 2, 1, 5]"
        },
        "expected": "#[1, 1, 2, 3, 5]",
        "unexpected": [
            "#[1, 2, 3, 1, 5]",
            "#[3, 1, 2, 5, 1]"
        ]
    },
    {
        "input": {
            "a": "#[10]"
        },
        "expected": "#[10]",
        "unexpected": [
            "#[0]",
            "#[10, 10]"
        ]
    },
    {
        "input": {
            "a": "#[4, 4, 4, 2, 2, 8]"
        },
        "expected": "#[2, 2, 4, 4, 4, 8]",
        "unexpected": [
            "#[2, 4, 4, 2, 4, 8]",
            "#[4, 2, 4, 2, 4, 8]",
            "#[2, 4, 2, 4, 4, 8]"
        ]
    }
]
-/