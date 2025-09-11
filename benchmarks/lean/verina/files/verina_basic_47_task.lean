-- <vc-preamble>
@[reducible, simp]
def arraySum_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
theorem eq_of_sub_zero_and_ge (a b : Int) : a = b → a - b = 0 ∧ a ≥ b := by
  omega
-- </vc-helpers>

-- <vc-definitions>
def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!
@[reducible, simp]
def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size

theorem arraySum_spec_satisfied (a: Array Int) (h_precond : arraySum_precond (a)) :
    arraySum_postcond (a) (arraySum (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5]"
        },
        "expected": 15,
        "unexpected": [
            14,
            10,
            16
        ]
    },
    {
        "input": {
            "a": "#[13, 14, 15, 16, 17]"
        },
        "expected": 75,
        "unexpected": [
            74,
            76,
            70
        ]
    },
    {
        "input": {
            "a": "#[-1, -2, -3]"
        },
        "expected": -6,
        "unexpected": [
            -5,
            -7,
            0
        ]
    },
    {
        "input": {
            "a": "#[10, -10]"
        },
        "expected": 0,
        "unexpected": [
            5,
            -5,
            10
        ]
    }
]
-/