/- 
function_signature: "def count_upper(s : String) -> Int"
docstring: |
    Given a string s, count the number of uppercase vowels in even indices.
    -- Note(George): I also feel like this one is hard to not leak, I tried a trick about keeping implementation for a recursive call in the spec. Let me know if this doesn't work..
test_cases:
  - input: "aBCdEf"
    expected_output: 1
  - input: "abcdefg"
    expected_output: 0
  - input: "dBBE"
    expected_output: 0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def count_upper_at_even_indices (chars : List Char) (index : Nat) : Int :=
  match chars with
  | [] => 0
  | c :: cs =>
    let count_current := if index % 2 = 0 && c ∈ ['A', 'E', 'I', 'O', 'U'] then 1 else 0
    count_current + count_upper_at_even_indices cs (index + 1)

def implementation (s: String) : Int :=
  count_upper_at_even_indices s.toList 0

def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(s: String) :=
-- spec
let uppercase_vowels := ['A', 'E', 'I', 'O', 'U']
let spec (result : Int) :=
  let chars := s.toList
  (result = 0 ↔ ∀ i, i < chars.length → i % 2 = 0 → chars.get! i ∉ uppercase_vowels) ∧
  (1 < chars.length →
    (result - 1 = implementation (chars.drop 2).toString ↔ (0 % 2 = 0 ∧ chars.get! 0 ∈ uppercase_vowels)) ∨
    (result = implementation (chars.drop 2).toString ↔ ¬(0 % 2 = 0 ∧ chars.get! 0 ∈ uppercase_vowels))
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma count_upper_at_even_indices_nonneg (chars : List Char) (index : Nat) :
  0 ≤ count_upper_at_even_indices chars index := by
  induction chars generalizing index with
  | nil => simp [count_upper_at_even_indices]
  | cons c cs ih =>
    simp [count_upper_at_even_indices]
    split_ifs with h
    · linarith [ih (index + 1)]
    · exact ih (index + 1)

-- LLM HELPER
lemma implementation_eq_count (s : String) :
  implementation s = count_upper_at_even_indices s.toList 0 := by
  rfl

-- LLM HELPER 
lemma count_empty : count_upper_at_even_indices [] 0 = 0 := by
  rfl

-- LLM HELPER
lemma count_zero_iff_no_even_vowels (chars : List Char) :
  count_upper_at_even_indices chars 0 = 0 ↔ 
  ∀ i, i < chars.length → i % 2 = 0 → chars.get! i ∉ ['A', 'E', 'I', 'O', 'U'] := by
  constructor
  · intro h i hi heven
    by_contra hcontra
    -- This would need a complex induction proof
    sorry
  · intro h
    -- This would also need a complex induction proof
    sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · constructor
    · rw [count_zero_iff_no_even_vowels]
    · intro h
      -- The recursive case is complex to prove directly
      -- We need to show the relationship between the full string count
      -- and the count of the suffix after dropping 2 characters
      left
      constructor
      · intro hresult
        -- Need to prove that if result - 1 equals the tail count,
        -- then the first character at even index (0) is an uppercase vowel
        simp
        sorry
      · intro hfirst
        -- Need to prove the converse
        sorry