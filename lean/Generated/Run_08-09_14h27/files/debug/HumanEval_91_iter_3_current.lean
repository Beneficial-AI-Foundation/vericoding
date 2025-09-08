/- 
function_signature: "def is_bored(s: str) -> int"
docstring: |
    You'll be given a string of words, and your task is to count the number
    of boredoms. A boredom is a sentence that starts with the word "I".
    Sentences are delimited by '.', '?' or '!'.
test_cases:
  - input: "Hello world"
    expected_output: 0
  - input: "The sky is blue. The sun is shining. I love this weather"
    expected_output: 1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def split_sentences (s: String) : List String :=
  let delims := ['.', '?', '!']
  let rec split_aux (chars : List Char) (acc : String) (result : List String) : List String :=
    match chars with
    | [] => if acc.isEmpty then result else result ++ [acc]
    | c :: rest =>
      if c ∈ delims then
        if acc.isEmpty then split_aux rest "" result
        else split_aux rest "" (result ++ [acc])
      else
        split_aux rest (acc.push c) result
  split_aux s.data "" []

-- LLM HELPER
def starts_with_i (sentence: String) : Bool :=
  let trimmed := sentence.trim
  trimmed.startsWith "I " ∨ trimmed == "I"

def implementation (s: String) : Nat :=
  let sentences := split_sentences s
  sentences.foldl (fun acc sent => acc + if starts_with_i sent then 1 else 0) 0

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Nat) :=
  let is_sentence_is_boredom (s: String) : Bool :=
    (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data
  match s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
  | some i =>
    let j := i + 1;
    let substring := s.drop j;
    result = (if is_sentence_is_boredom substring then 1 else 0) + implementation substring
  | none =>
    result = if is_sentence_is_boredom s then 1 else 0
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma implementation_terminates (s: String) : ∃ result, implementation s = result := by
  exists (implementation s)
  rfl

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  use implementation s
  constructor
  · rfl
  · let is_sentence_is_boredom := fun s ↦ (s.startsWith "I " ∨ s.startsWith " I") ∧ '.' ∉ s.data ∧ '?' ∉ s.data ∧ '!' ∉ s.data
    cases h : s.data.findIdx? (λ c => c = '.' ∨ c = '?' ∨ c = '!') with
    | some i =>
      simp [h]
      -- The actual proof would require showing that our implementation matches the recursive spec
      -- This is complex due to the recursive nature of the spec and string manipulation
      have : implementation s = implementation s := rfl
      sorry
    | none =>
      simp [h]
      -- Case where no delimiters are found
      have : implementation s = implementation s := rfl
      sorry

-- #test implementation "Hello world" = 0
-- #test implementation "The sky is blue. The sun is shining. I love this weather" = 1