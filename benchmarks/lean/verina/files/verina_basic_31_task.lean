/- 
-----Description-----
This task requires writing a Lean 4 method that converts a given string to uppercase. The method should replace every lowercase letter in the input string with its corresponding uppercase character while leaving all other characters unchanged. The output string must have the same length as the input string.

-----Input-----
The input consists of:
s: A string.

-----Output-----
The output is a string:
Returns a new string in which every lowercase letter from the input string is converted to uppercase, and all other characters are exactly the same as in the input string, ensuring the output string has the same length as the input.

-----Note-----
There are no preconditions since the method assumes that the input string is always valid (i.e., non-null).
-/

@[reducible, simp]
def toUppercase_precond (s : String) : Prop :=
  True

-- <vc-helpers>
def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)
-- </vc-helpers>

def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  sorry

@[reducible, simp]
def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))

theorem toUppercase_spec_satisfied (s: String) (h_precond : toUppercase_precond (s)) :
    toUppercase_postcond (s) (toUppercase (s) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "Hello, World!"
        },
        "expected": "HELLO, WORLD!",
        "unexpected": [
            "hello, world!",
            "HeLLo, WORld!"
        ]
    },
    {
        "input": {
            "s": "abc"
        },
        "expected": "ABC",
        "unexpected": [
            "AbC",
            "abc"
        ]
    },
    {
        "input": {
            "s": "ABC"
        },
        "expected": "ABC",
        "unexpected": [
            "abc",
            "aBC",
            "Abc"
        ]
    },
    {
        "input": {
            "s": "123!?@"
        },
        "expected": "123!?@",
        "unexpected": [
            "123!@?",
            "321!?@"
        ]
    },
    {
        "input": {
            "s": ""
        },
        "expected": "",
        "unexpected": [
            " ",
            "a"
        ]
    }
]
-/