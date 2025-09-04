/- 
function_signature: "def get_closest_vowel(s : str) -> str"
docstring: |
    You are given a word. Your task is to find the closest vowel that stands between
    two consonants from the right side of the word (case sensitive).

    Vowels in the beginning and ending doesn't count. Return empty string if you didn't
    find any vowel met the above condition.

    You may assume that the given string contains English letter only.
    Note: The "closest" is interpreted as the closest to the end of the word, not the closest to the consonants.
test_cases:
  - input: "yogurt"
    expected_output: "u"
  - input: "FULL"
    expected_output: "U"
  - input: "quick"
    expected_output: "i"
  - input: "ab"
    expected_output: ""
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (s: String) : String :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (fun c => c.isAlpha) →
  let is_consonant (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  (result = "" → ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]!) ∧
  (result ≠ "" →
    result.length = 1 ∧
    result.data[0]! ∈ s.data ∧
    ¬ is_consonant result.data[0]! ∧
    ∃ (i j k : Nat),
      i < j ∧ j < k ∧ k < s.length ∧
      is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
      result.data[0]! = s.data[j]! ∧
      (∀ (i' j' k' : Nat),
        i' < j' ∧ j' < k' ∧ k' < s.length ∧ is_consonant s.data[i']! ∧ ¬ is_consonant s.data[j']! ∧ is_consonant s.data[k']! →
        j' ≤ j)
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "yogurt" = "u"
-- #test implementation "FULL" = "U"
-- #test implementation "quick" = "i"
-- #test implementation "ab" = ""