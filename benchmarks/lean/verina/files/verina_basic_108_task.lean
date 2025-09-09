@[reducible, simp]
def below_zero_precond (operations : List Int) : Prop :=
  True

-- <vc-helpers>
def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList
-- </vc-helpers>

def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
  sorry

@[reducible, simp]
def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))

theorem below_zero_spec_satisfied (operations: List Int) (h_precond : below_zero_precond (operations)) :
    below_zero_postcond (operations) (below_zero (operations) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "operations": "[1, 2, 3]"
        },
        "expected": "(#[0, 1, 3, 6], false)",
        "unexpected": [
            "(#[0, 1, 3, 5], false)",
            "(#[0, 2, 3, 6], false)",
            "(#[0, 1, 3, 6], true)"
        ]
    },
    {
        "input": {
            "operations": "[-1, 2, -1]"
        },
        "expected": "(#[0, -1, 1, 0], true)",
        "unexpected": [
            "(#[0, -1, 1, 0], false)",
            "(#[0, -1, 0, 0], true)",
            "(#[0, -2, 1, 0], true)"
        ]
    },
    {
        "input": {
            "operations": "[]"
        },
        "expected": "(#[0], false)",
        "unexpected": [
            "(#[0], true)",
            "(#[0, 0], false)",
            "(#[0, 1], false)"
        ]
    },
    {
        "input": {
            "operations": "[0, 0, 0]"
        },
        "expected": "(#[0, 0, 0, 0], false)",
        "unexpected": [
            "(#[0, 0, 0, 0], true)",
            "(#[0, 0, 0], false)",
            "(#[0, 0, 1, 0], false)"
        ]
    },
    {
        "input": {
            "operations": "[10, -20, 5]"
        },
        "expected": "(#[0, 10, -10, -5], true)",
        "unexpected": [
            "(#[0, 10, -10, -5], false)",
            "(#[0, 10, -9, -5], true)",
            "(#[0, 10, -10, -6], true)"
        ]
    }
]
-/