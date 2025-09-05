/- 
-----Description-----
This problem involves determining the longest common prefix shared by two lists of characters. Given two sequences, the goal is to identify and return the maximal contiguous sequence of characters from the beginning of both lists that are identical.

-----Input-----
The input consists of:
• str1: A list of characters.
• str2: A list of characters.

-----Output-----
The output is a list of characters representing the longest common prefix of the two input lists. The output list satisfies the following conditions:
• Its length is less than or equal to the length of each input list.
• It is exactly the prefix of both str1 and str2.
• It is empty if the first characters of the inputs differ or if one of the lists is empty.

-----Note-----
It is assumed that both inputs are provided as valid lists of characters. The function always returns the correct longest common prefix based on the inputs.
-/

@[reducible, simp]
def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :=
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))

theorem LongestCommonPrefix_spec_satisfied (str1: List Char) (str2: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    LongestCommonPrefix_postcond (str1) (str2) (LongestCommonPrefix (str1) (str2) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

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
