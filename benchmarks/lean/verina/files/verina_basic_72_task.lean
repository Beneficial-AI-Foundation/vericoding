@[reducible, simp]
def append_precond (a : Array Int) (b : Int) : Prop :=
  True

-- <vc-helpers>
def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc
-- </vc-helpers>

def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  sorry

@[reducible, simp]
def append_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : append_precond (a) (b)) :=
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1

theorem append_spec_satisfied (a: Array Int) (b: Int) (h_precond : append_precond (a) (b)) :
    append_postcond (a) (b) (append (a) (b) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": 4
        },
        "expected": "#[1, 2, 3, 4]",
        "unexpected": [
            "#[1, 2, 3, 0]",
            "#[1, 2, 4, 3]",
            "#[4, 1, 2, 3]"
        ]
    },
    {
        "input": {
            "a": "#[]",
            "b": 0
        },
        "expected": "#[0]",
        "unexpected": [
            "#[1]",
            "#[]",
            "#[0, 0]"
        ]
    },
    {
        "input": {
            "a": "#[5, 6]",
            "b": -1
        },
        "expected": "#[5, 6, -1]",
        "unexpected": [
            "#[5, -1, 6]",
            "#[5, 6, 0]",
            "#[6, 5, -1]"
        ]
    },
    {
        "input": {
            "a": "#[0, 0, 0]",
            "b": 1
        },
        "expected": "#[0, 0, 0, 1]",
        "unexpected": [
            "#[1, 0, 0, 0]",
            "#[0, 1, 0, 0]",
            "#[0, 0, 1, 0]"
        ]
    },
    {
        "input": {
            "a": "#[-2, -3]",
            "b": -4
        },
        "expected": "#[-2, -3, -4]",
        "unexpected": [
            "#[-2, -4, -3]",
            "#[-2, -3, 0]",
            "#[-3, -2, -4]"
        ]
    }
]
-/