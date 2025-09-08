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
  intro c h
  have h_mem_filter : c ∈ s.data.filter p := by
    simp [List.asString_data] at h
    exact h
  exact (List.mem_filter.mp h_mem_filter).2

-- LLM HELPER
lemma filter_length_le (s : String) (p : Char → Bool) :
  (s.data.filter p |>.asString).length ≤ s.length := by
  simp [String.length]
  apply List.length_filter_le

-- LLM HELPER
lemma filter_contains_subset (s : String) (p : Char → Bool) (c : Char) :
  (s.data.filter p |>.asString).contains c → s.contains c := by
  simp [String.contains]
  intro h
  have h_mem_filter : c ∈ s.data.filter p := by
    simp [List.asString_data] at h
    exact h
  exact (List.mem_filter.mp h_mem_filter).1

-- LLM HELPER
lemma contains_filter_iff (s : String) (p : Char → Bool) (c : Char) :
  s.contains c ∧ p c = true → (s.data.filter p |>.asString).contains c := by
  simp [String.contains]
  intro h1 h2
  simp [List.asString_data]
  apply List.mem_filter.mpr
  exact ⟨h1, h2⟩

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
      · -- ∀ c, result.contains c → string.contains c ∧ ∀ c , string.contains c ∧ is_consonant c → (result.contains c)
        intro c h
        constructor
        · apply filter_contains_subset
          exact h
        · intro c' h'
          apply contains_filter_iff
          unfold is_consonant at h'
          exact h'

-- #test implementation "" = ""
-- #test implementation "cat" = "catac"
-- #test implementation "cata" = "catac"