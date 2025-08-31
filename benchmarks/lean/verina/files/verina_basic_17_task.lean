/- 
-----Description-----
This task requires writing a Lean 4 method that converts all uppercase characters in a given string to their lowercase equivalents while keeping the other characters unchanged. The output string must have the same length as the input string.

-----Input-----
The input consists of:
s: A string that may contain both uppercase and lowercase characters.

-----Output-----
The output is a string:
Returns a new string where every uppercase letter has been converted to lowercase, and every non-uppercase character remains exactly as in the input.

-----Note-----
There are no preconditions; the method is expected to work for any non-null string.
-/

@[reducible, simp]
def toLowercase_precond (s : String) : Prop :=
  True

-- <vc-helpers>
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)
-- </vc-helpers>

def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def toLowercase_postcond (s : String) (result: String) (h_precond : toLowercase_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))

theorem toLowercase_spec_satisfied (s: String) (h_precond : toLowercase_precond (s)) :
    toLowercase_postcond (s) (toLowercase (s) h_precond) h_precond := by
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
            "s": "Hello, World!"
        },
        "expected": "hello, world!",
        "unexpected": [
            "Hello, world!",
            "HELLO, WORLD!",
            "hello, World!"
        ]
    },
    {
        "input": {
            "s": "ABC"
        },
        "expected": "abc",
        "unexpected": [
            "ABC",
            "Abc",
            "aBC"
        ]
    },
    {
        "input": {
            "s": "abc"
        },
        "expected": "abc",
        "unexpected": [
            "ABC",
            "aBc",
            "abC"
        ]
    },
    {
        "input": {
            "s": ""
        },
        "expected": "",
        "unexpected": [
            " ",
            "empty",
            "null"
        ]
    },
    {
        "input": {
            "s": "1234!@"
        },
        "expected": "1234!@",
        "unexpected": [
            "1234!#",
            "12345!@"
        ]
    },
    {
        "input": {
            "s": "MixedCASE123"
        },
        "expected": "mixedcase123",
        "unexpected": [
            "Mixedcase123",
            "mixedCASE123",
            "MIXEDCASE123"
        ]
    }
]
-/