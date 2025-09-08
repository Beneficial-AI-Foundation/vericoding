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
(∀ i, i < result.length → result[i]!.containsSubstr substring ∧
∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result ∧
∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
-- program termination
∃ result, implementation strings substring = result ∧
spec result

-- LLM HELPER
lemma filter_mem_iff {α : Type*} (l : List α) (p : α → Bool) (x : α) :
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  constructor
  · intro h
    exact ⟨List.mem_of_mem_filter h, List.of_mem_filter h⟩
  · intro ⟨h1, h2⟩
    exact List.mem_filter.mpr ⟨h1, h2⟩

-- LLM HELPER
lemma filter_count_eq {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) (x : α) 
  (h : p x = true) : (l.filter p).count x = l.count x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons]
    cases h_pa : p a with
    | true => 
      simp only [List.count_cons]
      by_cases h' : a = x
      · simp [h']
        exact ih
      · simp [h', ih]
    | false =>
      simp only [List.count_cons]
      by_cases h' : a = x
      · simp [h']
        rw [h'] at h_pa
        rw [h_pa] at h
        contradiction
      · simp [h', ih]

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring
:= by
  unfold problem_spec implementation
  use strings.filter (fun s => s.containsSubstr substring)
  constructor
  · rfl
  · intro i hi
    constructor
    · -- Prove result[i]!.containsSubstr substring
      have h_mem := List.get_mem (strings.filter (fun s => s.containsSubstr substring)) ⟨i, hi⟩
      rw [filter_mem_iff] at h_mem
      exact h_mem.2
    · constructor
      · -- Prove ∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result
        intro j hj
        rw [filter_mem_iff]
        exact ⟨List.get_mem strings ⟨j, hj.1⟩, hj.2⟩
      · -- Prove ∀ j, j < result.length → result.count result[j]! = strings.count result[j]!
        intro j hj
        have h_mem := List.get_mem (strings.filter (fun s => s.containsSubstr substring)) ⟨j, hj⟩
        rw [filter_mem_iff] at h_mem
        exact filter_count_eq strings (fun s => s.containsSubstr substring) 
          (strings.filter (fun s => s.containsSubstr substring))[j]! h_mem.2

-- #test implementation [] "a" = []
-- #test implementation ["abc", "bacd", "cde", "array"] "a" = ["abc", "bacd", "array"]