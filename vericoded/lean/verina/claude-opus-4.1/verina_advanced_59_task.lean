import Mathlib
-- <vc-preamble>
@[reducible]
def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Helper functions for palindrome checking
-- LLM HELPER
def cleanString (s : String) : List Char :=
  s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower

-- LLM HELPER
def isPalindromeList (l : List Char) : Bool :=
  l = l.reverse
-- </vc-helpers>

-- <vc-definitions>
def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
  cleaned = cleaned.reverse
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
  unfold palindromeIgnoreNonAlnum_postcond palindromeIgnoreNonAlnum
  simp only [palindromeIgnoreNonAlnum_precond] at h_precond
  let cleaned := s.data.filter (fun c => c.isAlpha || c.isDigit) |>.map Char.toLower
  by_cases h : cleaned = cleaned.reverse
  · simp [h]
  · simp [h]
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