-- <vc-preamble>
@[reducible, simp]
def replace_precond (arr : Array Int) (k : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def replace_postcond (arr : Array Int) (k : Int) (result: Array Int) (h_precond : replace_precond (arr) (k)) :=
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
  (∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))

theorem replace_spec_satisfied (arr: Array Int) (k: Int) (h_precond : replace_precond (arr) (k)) :
    replace_postcond (arr) (k) (replace (arr) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "arr": "#[1, 5, 3, 10]",
            "k": 4
        },
        "expected": "#[1, -1, 3, -1]",
        "unexpected": [
            "#[1, 5, 3, 10]",
            "#[1, -1, 3, 10]"
        ]
    },
    {
        "input": {
            "arr": "#[-1, 0, 1, 2]",
            "k": 2
        },
        "expected": "#[-1, 0, 1, 2]",
        "unexpected": [
            "#[0, 0, 1, 2]",
            "#[-1, 0, 1, 1]"
        ]
    },
    {
        "input": {
            "arr": "#[100, 50, 100]",
            "k": 100
        },
        "expected": "#[100, 50, 100]",
        "unexpected": [
            "#[100, 50, -1]",
            "#[100, 50, 50]"
        ]
    },
    {
        "input": {
            "arr": "#[-5, -2, 0, 3]",
            "k": -3
        },
        "expected": "#[-5, -1, -1, -1]",
        "unexpected": [
            "#[-5, -2, -1, -1]",
            "#[-5, -1, 0, -1]"
        ]
    },
    {
        "input": {
            "arr": "#[1, 2, 3]",
            "k": 5
        },
        "expected": "#[1, 2, 3]",
        "unexpected": [
            "#[1, 3, 3]",
            "#[1, 2, -1]"
        ]
    }
]
-/