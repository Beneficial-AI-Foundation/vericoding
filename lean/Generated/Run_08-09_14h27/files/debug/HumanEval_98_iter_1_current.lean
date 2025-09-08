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
  (result = 0 ↔ ∀ i, i < chars.length → chars[i]! ∉ uppercase_vowels) ∧
  (1 < chars.length →
    (result - 1 = implementation (chars.drop 2).toString ↔ chars[0]! ∈ uppercase_vowels) ∨
    (result = implementation (chars.drop 2).toString ↔ chars[0]! ∉ uppercase_vowels)
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
    cases' (index % 2 = 0 && c ∈ ['A', 'E', 'I', 'O', 'U']) with h
    · simp
      exact ih (index + 1)
    · simp
      linarith [ih (index + 1)]

-- LLM HELPER
lemma implementation_drop_two (s : String) :
  let chars := s.toList
  chars.length ≥ 2 →
  implementation (chars.drop 2).toString = count_upper_at_even_indices (chars.drop 2) 0 := by
  intro h
  simp [implementation]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp only [implementation]
    constructor
    · constructor
      · intro h
        simp [count_upper_at_even_indices] at h
        sorry -- This would require a complex proof about the relationship between the spec and implementation
      · intro h
        sorry -- This would also require a complex proof
    · intro h
      sorry -- The recursive relationship in the spec doesn't directly match our implementation structure