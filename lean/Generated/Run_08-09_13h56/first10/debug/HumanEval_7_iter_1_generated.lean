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
(∀ i, i < result.length → result[i]!.containsSubstr substring →
∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result →
∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
-- program termination
∃ result, implementation strings substring = result ∧
spec result

-- LLM HELPER
lemma filter_mem_iff {α : Type*} (l : List α) (p : α → Bool) (x : α) :
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  simp [List.mem_filter]

-- LLM HELPER
lemma filter_count {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) (x : α) :
  (l.filter p).count x ≤ l.count x := by
  simp [List.count_filter]

-- LLM HELPER
lemma filter_count_eq {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) (x : α) 
  (h : p x = true) : (l.filter p).count x = l.count x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.filter, List.count_cons]
    by_cases h' : a = x
    · simp [h', h]
    · simp [h']
      exact ih

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring
:= by
  unfold problem_spec implementation
  use strings.filter (fun s => s.containsSubstr substring)
  constructor
  · rfl
  · intro i hi h1 j hj h2
    have : strings[j]! ∈ strings.filter (fun s => s.containsSubstr substring) := by
      rw [filter_mem_iff]
      constructor
      · exact List.get_mem strings j (Nat.lt_of_succ_le (Nat.succ_le_of_lt hj.1))
      · exact hj.2
    exact this

-- #test implementation [] "a" = []
-- #test implementation ["abc", "bacd", "cde", "array"] "a" = ["abc", "bacd", "array"]