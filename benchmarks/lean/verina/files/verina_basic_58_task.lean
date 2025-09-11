-- <vc-preamble>
@[reducible, simp]
def double_array_elements_precond (s : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def double_array_elements (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def double_array_elements_postcond (s : Array Int) (result: Array Int) (h_precond : double_array_elements_precond (s)) :=
  result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!

theorem double_array_elements_spec_satisfied (s: Array Int) (h_precond : double_array_elements_precond (s)) :
    double_array_elements_postcond (s) (double_array_elements (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]",
            "#[0]",
            "#[-1]"
        ]
    },
    {
        "input": {
            "s": "#[1, 2, 3, 4, 5]"
        },
        "expected": "#[2, 4, 6, 8, 10]",
        "unexpected": [
            "#[1, 2, 3, 4, 5]",
            "#[2, 4, 6, 8, 9]",
            "#[0, 4, 6, 8, 10]"
        ]
    },
    {
        "input": {
            "s": "#[0, -1, 5]"
        },
        "expected": "#[0, -2, 10]",
        "unexpected": [
            "#[0, -1, 5]",
            "#[1, -2, 10]",
            "#[0, 0, 10]"
        ]
    },
    {
        "input": {
            "s": "#[100]"
        },
        "expected": "#[200]",
        "unexpected": [
            "#[100]",
            "#[0]",
            "#[201]"
        ]
    },
    {
        "input": {
            "s": "#[-3, -4]"
        },
        "expected": "#[-6, -8]",
        "unexpected": [
            "#[3, -4]",
            "#[-6, -7]",
            "#[-6, -9]"
        ]
    }
]
-/