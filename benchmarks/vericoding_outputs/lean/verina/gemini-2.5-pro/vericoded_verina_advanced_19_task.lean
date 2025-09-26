import Mathlib
-- <vc-preamble>
@[reducible]
def isCleanPalindrome_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Normalize a character: keep only lowercase letters
def normalizeChar (c : Char) : Option Char := 
  if c.isAlpha then some c.toLower else none

-- LLM HELPER
-- Normalize a string into a list of lowercase alphabetic characters
def normalizeString (s : String) : List Char := 
  s.toList.filterMap normalizeChar
-- </vc-helpers>

-- <vc-definitions>
def isCleanPalindrome (s : String) (h_precond : isCleanPalindrome_precond (s)) : Bool :=
  let norm := normalizeString s
norm == norm.reverse
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def isCleanPalindrome_postcond (s : String) (result: Bool) (h_precond : isCleanPalindrome_precond (s)) : Prop :=
  let norm := normalizeString s
  (result = true → norm = norm.reverse) ∧
  (result = false → norm ≠ norm.reverse)

theorem isCleanPalindrome_spec_satisfied (s: String) (h_precond : isCleanPalindrome_precond (s)) :
    isCleanPalindrome_postcond (s) (isCleanPalindrome (s) h_precond) h_precond := by
  unfold isCleanPalindrome_postcond isCleanPalindrome
  dsimp
  simp [beq_iff_eq]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "s": "A man, a plan, a canal, Panama"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "No lemon, no melon"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "OpenAI"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "s": "Was it a car or a cat I saw?"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "s": "Hello, World!"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/