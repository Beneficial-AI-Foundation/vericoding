/- 
function_signature: "def split_words(txt)"
docstring: |
    Given a string of words, return a list of words split on whitespace, if no whitespaces exists in the text you
    should split on commas ',' if no commas exists you should return the number of lower-case letters with odd order in the
    alphabet, ord('a') = 0, ord('b') = 1, ... ord('z') = 25
test_cases:
  - input: "Hello world!"
    expected_output: ["Hello", "world!"]
  - input: "Hello,world!"
    expected_output: ["Hello", "world!"]
  - input: "abcdef"
    expected_output: 3
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def hasWhitespace (text: String) : Bool :=
  text.toList.any (· == ' ')

-- LLM HELPER
def hasComma (text: String) : Bool :=
  text.toList.any (· == ',')

-- LLM HELPER
def splitOnWhitespace (text: String) : List String :=
  text.splitOn " "

-- LLM HELPER
def splitOnComma (text: String) : List String :=
  text.splitOn ","

-- LLM HELPER
def isLowerCase (c: Char) : Bool :=
  c.val >= 97 && c.val <= 122

-- LLM HELPER
def charOrder (c: Char) : Nat :=
  if isLowerCase c then c.val.toNat - 97 else 0

-- LLM HELPER
def isOddOrder (c: Char) : Bool :=
  isLowerCase c && (charOrder c) % 2 == 1

-- LLM HELPER
def countOddOrderLowercase (text: String) : Nat :=
  text.toList.filter isOddOrder |>.length

def implementation (text: String) : Option (List String) × Option Nat :=
  if hasWhitespace text then
    (some (splitOnWhitespace text), none)
  else if hasComma text then
    (some (splitOnComma text), none)
  else
    (none, some (countOddOrderLowercase text))

-- LLM HELPER
def problem_spec_simple (impl: String → Option (List String) × Option Nat) (text: String) : Prop :=
  let result := impl text
  let words := result.fst
  let ord := result.snd
  -- Basic correctness properties
  (hasWhitespace text → ∃ lst, words = some lst ∧ ord = none) ∧
  (¬hasWhitespace text ∧ hasComma text → ∃ lst, words = some lst ∧ ord = none) ∧
  (¬hasWhitespace text ∧ ¬hasComma text → ∃ num, ord = some num ∧ words = none)

def problem_spec
-- function signature
-- return a tuple of Option (List String) and Option Nat
(impl: String → Option (List String) × Option Nat)
-- inputs
(text: String) :=
-- spec
let spec (result: Option (List String) × Option Nat) :=
  -- both cannot be None
  let words := result.fst;
  let ord := result.snd;
  0 < text.length →
  ¬ (words = none ∧ ord = none) ∧
    (words = none ↔ ¬hasWhitespace text ∧ ¬hasComma text) ∧
    (∀ num, ord = some num → num = countOddOrderLowercase text) ∧
    (∀ lst, words = some lst → lst.length > 0) ∧
    (hasWhitespace text → ∃ lst, words = some lst) ∧
    (¬hasWhitespace text ∧ hasComma text → ∃ lst, words = some lst)
-- program terminates
∃ result, impl text = result ∧
-- return value satisfies spec
spec result

theorem correctness
(text: String)
: problem_spec implementation text := by
  use implementation text
  constructor
  · rfl
  · intro h_len
    constructor
    · -- Not both none
      simp [implementation]
      by_cases h1 : hasWhitespace text
      · simp [h1]
      · by_cases h2 : hasComma text
        · simp [h1, h2]
        · simp [h1, h2]
    · constructor
      · -- words = none iff condition
        constructor
        · intro h_words_none
          simp [implementation] at h_words_none
          by_cases h1 : hasWhitespace text
          · simp [h1] at h_words_none
          · by_cases h2 : hasComma text
            · simp [h1, h2] at h_words_none
            · simp [h1, h2]
        · intro h_cond
          simp [implementation]
          simp [h_cond]
      · constructor
        · -- ord condition
          intro num h_ord
          simp [implementation] at h_ord
          by_cases h1 : hasWhitespace text
          · simp [h1] at h_ord
          · by_cases h2 : hasComma text
            · simp [h1, h2] at h_ord
            · simp [h1, h2] at h_ord
              exact h_ord
        · constructor
          · -- lst length > 0
            intro lst h_words
            simp [implementation] at h_words
            by_cases h1 : hasWhitespace text
            · simp [h1] at h_words
              simp [splitOnWhitespace] at h_words
              rw [← h_words]
              simp [String.splitOn]
              exact List.length_pos_of_ne_nil (String.splitOn_ne_nil text " ")
            · by_cases h2 : hasComma text
              · simp [h1, h2] at h_words
                simp [splitOnComma] at h_words
                rw [← h_words]
                simp [String.splitOn]
                exact List.length_pos_of_ne_nil (String.splitOn_ne_nil text ",")
              · simp [h1, h2] at h_words
          · constructor
            · -- hasWhitespace implies words exists
              intro h_ws
              simp [implementation, h_ws]
              use splitOnWhitespace text
              rfl
            · -- no whitespace but has comma implies words exists
              intro h_cond
              simp [implementation]
              simp [h_cond]
              use splitOnComma text
              rfl