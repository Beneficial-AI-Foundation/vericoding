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
  (result = 0 ↔ ∀ i, i < s.length → i % 2 = 0 → s.data[i]?.getD 'A' ∉ uppercase_vowels) ∧
  (1 < s.length →
    (result - 1 = implementation (s.data.drop 2).toString ↔ (0 % 2 = 0 ∧ s.data[0]?.getD 'A' ∈ uppercase_vowels)) ∨
    (result = implementation (s.data.drop 2).toString ↔ ¬(0 % 2 = 0 ∧ s.data[0]?.getD 'A' ∈ uppercase_vowels))
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
    · have ih_pos : 0 ≤ count_upper_at_even_indices cs (index + 1) := ih (index + 1)
      linarith
    · exact ih (index + 1)

-- LLM HELPER
lemma implementation_eq_count (s : String) :
  implementation s = count_upper_at_even_indices s.toList 0 := by
  rfl

-- LLM HELPER 
lemma count_empty : count_upper_at_even_indices [] 0 = 0 := by
  rfl

-- LLM HELPER
lemma count_zero_iff_no_even_vowels (s : String) :
  implementation s = 0 ↔ 
  ∀ i, i < s.length → i % 2 = 0 → s.data[i]?.getD 'A' ∉ ['A', 'E', 'I', 'O', 'U'] := by
  simp [implementation]
  constructor
  · intro h i hi heven
    by_contra h_contra
    -- This would require detailed proof showing contradiction
    sorry
  · intro h
    -- This would require detailed proof showing the count is 0
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
    · exact count_zero_iff_no_even_vowels s
    · intro h
      by_cases h_case : (0 % 2 = 0 ∧ s.data[0]?.getD 'A' ∈ ['A', 'E', 'I', 'O', 'U'])
      · left
        constructor
        · intro hresult
          exact h_case
        · intro h_vowel
          sorry
      · right
        constructor
        · intro hresult
          exact h_case
        · intro h_not_vowel
          sorry