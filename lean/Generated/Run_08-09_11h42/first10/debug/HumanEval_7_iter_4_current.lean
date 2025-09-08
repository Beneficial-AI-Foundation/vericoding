/- 
function_signature: "def filter_by_substring(strings: List[str], substring: str) -> List[str]"
docstring: |
  Filter an input list of strings only for ones that contain given substring
test_cases:
  - input:
    - []
    - "a"
    expected_output: []
  - input:
    - ["abc", "bacd", "cde", "array"]
    - "a"
    expected_output: ["abc", "bacd", "array"]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (strings: List String) (substring: String): List String :=
  strings.filter (fun s => s.containsSubstr substring)

def problem_spec
-- function signature
(implementation: List String → String → List String)
-- inputs
(strings: List String)
(substring: String)
:=
-- spec
let spec (result: List String) :=
(∀ i, i < result.length → result[i]!.containsSubstr substring) ∧
(∀ s ∈ strings, s.containsSubstr substring → s ∈ result) ∧
(∀ s ∈ result, strings.count s = result.count s);
-- program termination
∃ result, implementation strings substring = result ∧
spec result

-- LLM HELPER
lemma filter_preserves_containsSubstr (strings: List String) (substring: String) :
  ∀ s ∈ strings.filter (fun x => x.containsSubstr substring), s.containsSubstr substring := by
  intros s hs
  rw [List.mem_filter] at hs
  exact hs.2

-- LLM HELPER
lemma filter_contains_all_matching (strings: List String) (substring: String) :
  ∀ s ∈ strings, s.containsSubstr substring → s ∈ strings.filter (fun x => x.containsSubstr substring) := by
  intros s hs hcontains
  rw [List.mem_filter]
  exact ⟨hs, hcontains⟩

-- LLM HELPER
lemma filter_preserves_count (strings: List String) (substring: String) (s: String) :
  s ∈ strings.filter (fun x => x.containsSubstr substring) →
  strings.count s = (strings.filter (fun x => x.containsSubstr substring)).count s := by
  intro h
  rw [List.mem_filter] at h
  have h_contains := h.2
  rw [List.count_filter]
  simp [h_contains]

-- LLM HELPER
lemma get_bang_mem (l : List String) (i : Nat) (h : i < l.length) : 
  l[i]! ∈ l := by
  rw [List.getElem!_def]
  simp [h]
  exact List.get_mem l ⟨i, h⟩

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring
:= by
  unfold problem_spec implementation
  use strings.filter (fun s => s.containsSubstr substring)
  constructor
  · rfl
  constructor
  · intros i hi
    have h_mem := get_bang_mem (strings.filter (fun s => s.containsSubstr substring)) i hi
    exact filter_preserves_containsSubstr strings substring (strings.filter (fun s => s.containsSubstr substring))[i]! h_mem
  constructor
  · exact filter_contains_all_matching strings substring
  · intros s hs
    exact filter_preserves_count strings substring s hs

-- #test implementation [] "a" = []
-- #test implementation ["abc", "bacd", "cde", "array"] "a" = ["abc", "bacd", "array"]