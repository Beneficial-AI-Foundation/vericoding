@[reducible, simp]
def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def replaceChars (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  sorry

@[reducible, simp]
def replaceChars_postcond (s : String) (oldChar : Char) (newChar : Char) (result: String) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :=
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < cs.length →
    (cs[i]! = oldChar → cs'[i]! = newChar) ∧
    (cs[i]! ≠ oldChar → cs'[i]! = cs[i]!))

theorem replaceChars_spec_satisfied (s: String) (oldChar: Char) (newChar: Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    replaceChars_postcond (s) (oldChar) (newChar) (replaceChars (s) (oldChar) (newChar) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "hello, world!",
            "oldChar": ",",
            "newChar": ";"
        },
        "expected": "hello; world!",
        "unexpected": [
            "hello, world!",
            "hello world!",
            "hello;world!"
        ]
    },
    {
        "input": {
            "s": "a,b.c",
            "oldChar": ",",
            "newChar": ":"
        },
        "expected": "a:b.c",
        "unexpected": [
            "a,b.c",
            "a;b.c",
            "ab:c"
        ]
    },
    {
        "input": {
            "s": "hello, world!",
            "oldChar": "o",
            "newChar": "O"
        },
        "expected": "hellO, wOrld!",
        "unexpected": [
            "hello, world!",
            "hellO, world!",
            "hello, wOrld!"
        ]
    },
    {
        "input": {
            "s": "",
            "oldChar": "x",
            "newChar": "y"
        },
        "expected": "",
        "unexpected": [
            " ",
            "abc"
        ]
    },
    {
        "input": {
            "s": "test",
            "oldChar": "x",
            "newChar": "y"
        },
        "expected": "test",
        "unexpected": [
            "testy",
            "tset",
            "yxest"
        ]
    },
    {
        "input": {
            "s": "unchanged",
            "oldChar": "u",
            "newChar": "u"
        },
        "expected": "unchanged",
        "unexpected": [
            "nchanged",
            "unchanged!",
            "unchangEd"
        ]
    },
    {
        "input": {
            "s": "aaa",
            "oldChar": "a",
            "newChar": "b"
        },
        "expected": "bbb",
        "unexpected": [
            "aaa",
            "abb",
            "bba"
        ]
    }
]
-/