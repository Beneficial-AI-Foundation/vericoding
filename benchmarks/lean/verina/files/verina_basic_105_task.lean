@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size

-- <vc-helpers>
def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c
-- </vc-helpers>

def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  sorry

@[reducible, simp]
def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayProduct_precond (a) (b)) :=
  (result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)

theorem arrayProduct_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    arrayProduct_postcond (a) (b) (arrayProduct (a) (b) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[4, 5]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[4, 5, 6]"
        },
        "expected": "#[4, 10, 18]",
        "unexpected": [
            "#[4, 10, 17]",
            "#[0, 10, 18]",
            "#[4, 10, 20]"
        ]
    },
    {
        "input": {
            "a": "#[0, 0, 0]",
            "b": "#[1, 2, 3]"
        },
        "expected": "#[0, 0, 0]",
        "unexpected": [
            "#[1, 0, 0]",
            "#[0, 1, 0]",
            "#[0, 0, 1]"
        ]
    },
    {
        "input": {
            "a": "#[-1, 2, -3]",
            "b": "#[3, -4, 5]"
        },
        "expected": "#[-3, -8, -15]",
        "unexpected": [
            "#[-3, -8, -14]",
            "#[-3, -7, -15]",
            "#[-2, -8, -15]"
        ]
    },
    {
        "input": {
            "a": "#[2]",
            "b": "#[10]"
        },
        "expected": "#[20]",
        "unexpected": [
            "#[10]",
            "#[0]",
            "#[30]"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3, 4]",
            "b": "#[2, 2, 2, 2]"
        },
        "expected": "#[2, 4, 6, 8]",
        "unexpected": [
            "#[2, 4, 6, 9]",
            "#[1, 4, 6, 8]",
            "#[2, 5, 6, 8]"
        ]
    }
]
-/