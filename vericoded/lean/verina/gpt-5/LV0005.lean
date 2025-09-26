import Mathlib
-- <vc-preamble>
@[reducible]
def allVowels_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def toLower (c : Char) : Char :=
  if h : 'A' ≤ c ∧ c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

-- LLM HELPER
def normalize_str (s : String) : List Char :=
  s.data.map toLower
-- </vc-helpers>

-- <vc-definitions>
def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  let chars := normalize_str s
  List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v)
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def allVowels_postcond (s : String) (result: Bool) (h_precond : allVowels_precond (s)) : Prop :=
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))

theorem allVowels_spec_satisfied (s: String) (h_precond : allVowels_precond (s)) :
    allVowels_postcond (s) (allVowels (s) h_precond) h_precond := by
  dsimp [allVowels_postcond, allVowels]
  exact Iff.rfl
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "education"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "education123"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "AEIOU"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "hello"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": ""
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": "apple orange union"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    }
]
-/