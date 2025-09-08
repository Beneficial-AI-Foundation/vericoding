/- 
function_signature: "def remove_vowels(string: str) -> Nat"
docstring: |
    Write a function vowels_count which takes a string representing
    a word as input and returns the number of vowels in the string.
    Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
    vowel, but only when it is at the end of the given word.
test_cases:
  - input: "abcde"
    expected_output: 2
  - input: "ACEDY"
    expected_output: 3
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def isVowel (c : Char) : Bool :=
  let vowels := "aeiouAEIOU"
  vowels.contains c

-- LLM HELPER
def isY (c : Char) : Bool := c = 'y' ∨ c = 'Y'

def implementation (string: String) : Nat :=
  if string.length = 0 then 0
  else if string.length = 1 then
    if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
  else
    let firstChar := string.data[0]!
    let restString := string.drop 1
    let firstCount := if isVowel firstChar then 1 else 0
    let lastChar := string.data[string.length - 1]!
    let isLastY := isY lastChar
    if string.length ≥ 2 ∧ isLastY then
      -- Y at end counts as vowel, but we need to handle it specially
      -- Count all vowels except Y, then add 1 for the final Y
      string.data.foldl (fun acc c => 
        if isVowel c then acc + 1 
        else if isY c ∧ c = lastChar then acc + 1
        else acc) 0
    else
      -- No Y at end, just count regular vowels
      string.data.foldl (fun acc c => if isVowel c then acc + 1 else acc) 0

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
let isVowel (c : Char) :=
  let vowels := "aeiouAEIOU"
  vowels.contains c
let isY (c : Char) := c = 'y' ∨ c = 'Y'
-- spec
let spec (result: Nat) :=
string.data.all (fun c => c.isAlpha) →
if string.length = 1 then
  result = if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
else
  result = (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma string_length_drop_one (s : String) (h : s.length > 0) : 
  (s.drop 1).length = s.length - 1 := by
  simp [String.drop, String.length]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    by_cases h : s.length = 1
    · simp [h]
      sorry -- This requires a more complex proof about the implementation matching the spec
    · simp [h]
      sorry -- This also requires showing the recursive structure matches

-- #test implementation "abcde" = 2
-- #test implementation "ACEDY" = 3