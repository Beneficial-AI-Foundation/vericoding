/- 
-----Description-----
This task requires writing a Lean 4 method that takes a given string and returns a new string where every occurrence of a space, comma, or dot is replaced with a colon. The transformation must preserve the original string’s length and leave all other characters unmodified.

-----Input-----
The input consists of:
s: A string.

-----Output-----
The output is a string:
- The returned string must have the same length as the input string.
- Every space, comma, or dot in the input string is replaced with a colon.
- All other characters remain unchanged.

-----Note-----
There are no preconditions; the input string is assumed to be non-null.
-/

@[reducible, simp]
def replaceWithColon_precond (s : String) : Prop :=
  True

-- <vc-helpers>
def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false
-- </vc-helpers>

def replaceWithColon (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def replaceWithColon_postcond (s : String) (result: String) (h_precond : replaceWithColon_precond (s)) :=
  let cs := s.toList
  let cs' := result.toList
  result.length = s.length ∧
  (∀ i, i < s.length →
    (isSpaceCommaDot cs[i]! → cs'[i]! = ':') ∧
    (¬isSpaceCommaDot cs[i]! → cs'[i]! = cs[i]!))

theorem replaceWithColon_spec_satisfied (s: String) (h_precond : replaceWithColon_precond (s)) :
    replaceWithColon_postcond (s) (replaceWithColon (s) h_precond) h_precond := by
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
            "s": "Hello, world. How are you?"
        },
        "expected": "Hello::world::How:are:you?",
        "unexpected": [
            "Hello,world,How,are,you?",
            "Hello: world: How: are: you?"
        ]
    },
    {
        "input": {
            "s": "No-changes!"
        },
        "expected": "No-changes!",
        "unexpected": [
            "No changes!",
            "No\u2013changes!"
        ]
    },
    {
        "input": {
            "s": ",. "
        },
        "expected": ":::",
        "unexpected": [
            "::",
            ";:;",
            "::: "
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
