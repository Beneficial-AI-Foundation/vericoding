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
  sorry

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