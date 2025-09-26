import Mathlib
-- <vc-preamble>
@[reducible]
def reverseString_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def reverseString (s : String) (h_precond : reverseString_precond (s)) : String :=
  String.mk (s.toList.reverse)
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def reverseString_postcond (s : String) (result: String) (h_precond : reverseString_precond (s)) : Prop :=
  result.length = s.length ∧ result.toList = s.toList.reverse

theorem reverseString_spec_satisfied (s: String) (h_precond : reverseString_precond (s)) :
    reverseString_postcond (s) (reverseString (s) h_precond) h_precond := by
  dsimp [reverseString_postcond, reverseString]
  constructor
  ·
    have hlen : s.toList.length = s.length := by
      simpa [String.length_mk] using congrArg String.length (String.mk_toList s)
    calc
      (String.mk (s.toList.reverse)).length
          = (s.toList.reverse).length := by simpa [String.length_mk]
      _ = s.toList.length := by simpa [List.length_reverse]
      _ = s.length := hlen
  ·
    rfl
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "hello"
        },
        "expected": "olleh",
        "unexpected": [
            "hello",
            "helo",
            "hell"
        ]
    },
    {
        "input": {
            "s": "a"
        },
        "expected": "a",
        "unexpected": [
            "",
            "aa"
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
    },
    {
        "input": {
            "s": "racecar"
        },
        "expected": "racecar",
        "unexpected": [
            "rceacar",
            "raeccar"
        ]
    },
    {
        "input": {
            "s": "Lean"
        },
        "expected": "naeL",
        "unexpected": [
            "Lean",
            "aenL"
        ]
    }
]
-/