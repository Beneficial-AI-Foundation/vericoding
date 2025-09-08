/- 
function_signature: "def remove_vowels(string: str) -> string"
docstring: |
    remove_vowels is a function that takes string and returns string without vowels.
test_cases:
  - input: ""
    expected_output: ""
  - input: "abcdef\nghijklm"
    expected_output: "bcdf\nghjklm"
  - input: "abcdef"
    expected_output: "bcdf"
  - input: "aaaaa"
    expected_output: ""
  - input: "aaBAA"
    expected_output: "B"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : String :=
  let vowels := "aeiouAEIOU"
  string.data.filter (fun c => not (vowels.contains c)) |>.asString

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
let is_consonant (c: Char): Bool :=
  let vowels := "aeiouAEIOU"
  not (vowels.contains c);
-- spec
let spec (result: String) :=
result.all (λ c => is_consonant c) ∧ result.length ≤ string.length ∧
∀ c, result.contains c → string.contains c ∧
∀ c , string.contains c ∧ is_consonant c → (result.contains c);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma filter_all_chars (s : String) (p : Char → Bool) : 
  (s.data.filter p |>.asString).all p = true := by
  simp [String.all_iff]

-- LLM HELPER
lemma filter_length_le (s : String) (p : Char → Bool) :
  (s.data.filter p |>.asString).length ≤ s.length := by
  simp [String.length_eq]
  apply List.length_filter_le

-- LLM HELPER
lemma filter_contains_subset (s : String) (p : Char → Bool) (c : Char) :
  (s.data.filter p |>.asString).contains c → s.contains c := by
  simp [String.contains_iff_mem]
  intro h
  apply List.mem_of_mem_filter h

-- LLM HELPER
lemma contains_filter_iff (s : String) (p : Char → Bool) (c : Char) :
  s.contains c ∧ p c = true → (s.data.filter p |>.asString).contains c := by
  simp [String.contains_iff_mem]
  intro h1 h2
  apply List.mem_filter.mpr
  constructor
  · exact h1
  · exact h2

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec implementation
  simp only []
  use s.data.filter (fun c => not ("aeiouAEIOU".contains c)) |>.asString
  constructor
  · rfl
  · constructor
    · -- result.all (λ c => is_consonant c)
      unfold is_consonant
      apply filter_all_chars
    · constructor
      · -- result.length ≤ string.length
        apply filter_length_le
      · constructor
        · -- ∀ c, result.contains c → string.contains c
          intro c h
          apply filter_contains_subset
          exact h
        · -- ∀ c , string.contains c ∧ is_consonant c → (result.contains c)
          intro c h
          apply contains_filter_iff
          unfold is_consonant at h
          constructor
          · exact h.1
          · exact h.2

-- #test implementation "" = ""
-- #test implementation "cat" = "catac"
-- #test implementation "cata" = "catac"