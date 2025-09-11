-- <vc-preamble>
@[reducible, simp]
def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :=
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))

theorem LongestCommonPrefix_spec_satisfied (str1: List Char) (str2: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    LongestCommonPrefix_postcond (str1) (str2) (LongestCommonPrefix (str1) (str2) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "str1": "['a', 'b', 'c']",
            "str2": "['a', 'b', 'd']"
        },
        "expected": "['a', 'b']",
        "unexpected": [
            "['a']",
            "['a', 'b', 'c']"
        ]
    },
    {
        "input": {
            "str1": "['x', 'y', 'z']",
            "str2": "['x', 'y', 'z']"
        },
        "expected": "['x', 'y', 'z']",
        "unexpected": [
            "['x', 'y']",
            "['x', 'z']"
        ]
    },
    {
        "input": {
            "str1": "['w', 'o']",
            "str2": "['w', 'o', 'w']"
        },
        "expected": "['w', 'o']",
        "unexpected": [
            "['w']",
            "['o']",
            "['w', 'o', 'w']"
        ]
    },
    {
        "input": {
            "str1": "['a', 'x']",
            "str2": "['b', 'y']"
        },
        "expected": "[]",
        "unexpected": [
            "['a']",
            "['b']"
        ]
    },
    {
        "input": {
            "str1": "[]",
            "str2": "['h', 'e', 'l', 'l', 'o']"
        },
        "expected": "[]",
        "unexpected": [
            "['h']",
            "['e']"
        ]
    }
]
-/