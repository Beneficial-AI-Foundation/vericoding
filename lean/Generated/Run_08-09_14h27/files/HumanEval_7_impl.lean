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
(∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result) ∧
(∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
-- program termination
∃ result, implementation strings substring = result ∧
spec result

-- LLM HELPER
lemma filter_preserves_containsSubstr (strings: List String) (substring: String) :
  ∀ x ∈ strings.filter (fun s => s.containsSubstr substring), x.containsSubstr substring := by
  intros x hx
  rw [List.mem_filter] at hx
  exact hx.2

-- LLM HELPER
lemma filter_contains_all_matching (strings: List String) (substring: String) :
  ∀ x ∈ strings, x.containsSubstr substring → x ∈ strings.filter (fun s => s.containsSubstr substring) := by
  intros x hx_mem hx_contains
  rw [List.mem_filter]
  exact ⟨hx_mem, hx_contains⟩

-- LLM HELPER
lemma filter_preserves_count (strings: List String) (substring: String) :
  ∀ x, (strings.filter (fun s => s.containsSubstr substring)).count x = 
       if x.containsSubstr substring then strings.count x else 0 := by
  intro x
  rw [List.count_filter]
  by_cases h : x.containsSubstr substring
  · simp [h]
  · simp [h]

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring
:= by
  unfold problem_spec implementation
  use strings.filter (fun s => s.containsSubstr substring)
  constructor
  · rfl
  · constructor
    · intros i hi
      have h_get := List.get_mem (strings.filter (fun s => s.containsSubstr substring)) ⟨i, hi⟩
      apply filter_preserves_containsSubstr strings substring
      convert h_get
      simp [List.getElem_eq_get]
    · constructor
      · intros j ⟨hj_bound, hj_contains⟩
        apply filter_contains_all_matching strings substring
        · exact List.get_mem strings ⟨j, hj_bound⟩
        · exact hj_contains
      · intros j hj_bound
        have filtered := strings.filter (fun s => s.containsSubstr substring)
        have h_mem := List.get_mem filtered ⟨j, hj_bound⟩
        have h_contains := filter_preserves_containsSubstr strings substring filtered[j]! h_mem
        rw [filter_preserves_count]
        rw [if_pos h_contains]

-- #test implementation [] "a" = []
-- #test implementation ["abc", "bacd", "cde", "array"] "a" = ["abc", "bacd", "array"]