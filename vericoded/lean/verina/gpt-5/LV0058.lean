import Mathlib
-- <vc-preamble>
@[reducible]
def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
  decide (cleaned = cleaned.reverse)
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def palindromeIgnoreNonAlnum_postcond (s : String) (result: Bool) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Prop :=
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
let forward := cleaned
let backward := cleaned.reverse

if result then
  forward = backward
else
  forward ≠ backward

theorem palindromeIgnoreNonAlnum_spec_satisfied (s: String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    palindromeIgnoreNonAlnum_postcond (s) (palindromeIgnoreNonAlnum (s) h_precond) h_precond := by
  classical
  set cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower with hclean
  by_cases h : cleaned = cleaned.reverse
  · simpa [palindromeIgnoreNonAlnum_postcond, palindromeIgnoreNonAlnum, h, hclean] using h
  · simpa [palindromeIgnoreNonAlnum_postcond, palindromeIgnoreNonAlnum, h, hclean] using h
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": ""
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "A man, a plan, a canal: Panama"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "race a car"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": "No 'x' in Nixon"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "abc!!cba?"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "Hello, world!"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/