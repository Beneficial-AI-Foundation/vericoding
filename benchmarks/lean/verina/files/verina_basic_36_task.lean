-- <vc-preamble>
@[reducible, simp]
def replaceWithColon_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replaceWithColon (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
  sorry
-- </vc-theorems>

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