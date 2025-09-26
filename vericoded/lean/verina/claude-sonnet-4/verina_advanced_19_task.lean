import Mathlib
-- <vc-preamble>
@[reducible]
def isCleanPalindrome_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Check if a character is an uppercase alphabet letter
def isUpperAlpha (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

-- Check if a character is a lowercase alphabet letter
def isLowerAlpha (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

-- Determine if a character is alphabetic
def isAlpha (c : Char) : Bool :=
  isUpperAlpha c ∨ isLowerAlpha c

-- Convert a single character to lowercase
def toLower (c : Char) : Char :=
  if isUpperAlpha c then Char.ofNat (c.toNat + 32) else c

-- Normalize a character: keep only lowercase letters
def normalizeChar (c : Char) : Option Char :=
  if isAlpha c then some (toLower c) else none

-- Normalize a string into a list of lowercase alphabetic characters
def normalizeString (s : String) : List Char :=
  s.toList.foldr (fun c acc =>
    match normalizeChar c with
    | some c' => c' :: acc
    | none    => acc
  ) []

-- Reverse the list
def reverseList (xs : List Char) : List Char :=
  xs.reverse
-- </vc-helpers>

-- <vc-definitions>
def isCleanPalindrome (s : String) (h_precond : isCleanPalindrome_precond (s)) : Bool :=
  let norm := normalizeString s
  norm = norm.reverse
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def isCleanPalindrome_postcond (s : String) (result: Bool) (h_precond : isCleanPalindrome_precond (s)) : Prop :=
  let norm := normalizeString s
  (result = true → norm = norm.reverse) ∧
  (result = false → norm ≠ norm.reverse)

theorem isCleanPalindrome_spec_satisfied (s: String) (h_precond : isCleanPalindrome_precond (s)) :
    isCleanPalindrome_postcond (s) (isCleanPalindrome (s) h_precond) h_precond := by
  unfold isCleanPalindrome_postcond
  unfold isCleanPalindrome
  simp only []
  let norm := normalizeString s
  by_cases h : norm = norm.reverse
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