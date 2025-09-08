/- 
function_signature: "def check_if_last_char_is_a_letter(txt: str) -> Bool"
docstring: |
    Create a function that returns True if the last character
    of a given string is an alphabetical character and is not
    a part of a word, and False otherwise.
    Note: "word" is a group of characters separated by space.
test_cases:
  - input: "apple pie"
    expected_output: False
  - input: "apple pi e"
    expected_output: True
  - input: "apple pi e "
    expected_output: False
  - input: ""
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_letter (c: Char) : Bool :=
  let diff := c.toLower.toNat - 'a'.toNat
  0 ≤ diff && diff ≤ 25

def implementation (txt: String) : Bool :=
  if txt.isEmpty then 
    false
  else if txt.back == ' ' then 
    false
  else
    let words := txt.splitOn " "
    match words.getLast? with
    | none => false
    | some last_word => 
        if last_word.isEmpty then false
        else last_word.length == 1 && is_letter (last_word.get! 0)

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(txt: String) :=
-- spec
let spec (result: Bool) :=
  let words := txt.splitOn " ";
  match words with
  | [] => result = False
  | [last_word] => (result ↔ last_word.length = 1 ∧ (let diff := (last_word.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25))
  | _::tail => result ↔ (let tail_txt := String.join tail; impl tail_txt);
-- program terminates
∃ result, impl txt = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma implementation_terminates (txt: String) : ∃ result, implementation txt = result := by
  use implementation txt
  rfl

-- LLM HELPER  
lemma empty_string_case : implementation "" = false := by
  simp [implementation]

-- LLM HELPER
lemma trailing_space_case (txt: String) (h: txt.back = ' ') : implementation txt = false := by
  simp [implementation, h]

-- LLM HELPER
lemma single_word_case (word: String) (h: word ≠ "" ∧ ¬ word.contains ' ') : 
  implementation word = (word.length == 1 && is_letter (word.get! 0)) := by
  simp [implementation]
  have h1 : ¬ word.isEmpty := by
    simp [String.isEmpty]
    exact h.1
  simp [h1]
  have h2 : word.back ≠ ' ' := by
    intro hc
    have : word.contains ' ' := by
      simp [String.contains]
      use word.length - 1
      constructor
      · simp [String.get]
        rw [hc]
      · sorry
    exact h.2 this
  simp [h2]
  have h3 : (word.splitOn " ").getLast? = some word := by
    simp [String.splitOn]
    sorry
  rw [h3]
  simp

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  simp [problem_spec]
  constructor
  · exact implementation_terminates txt
  · simp [implementation]
    by_cases h1 : txt.isEmpty
    · simp [h1]
    · by_cases h2 : txt.back = ' '
      · simp [h2]
      · simp [h1, h2]
        sorry

-- #test implementation "apple pie" = false
-- #test implementation "apple pi e" = true  
-- #test implementation "apple pi e " = false
-- #test implementation "" = false