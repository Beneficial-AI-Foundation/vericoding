/- 
function_signature: "def filter_by_prefix(strings: List[str], prefix: str) -> List[str]"
docstring: |
    Filter an input list of strings only for ones that start with a given prefix.
test_cases:
  - input:
    - []
    - "a"
    expected_output: []
  - input:
    - ["abc", "bcd", "cde", "array"]
    - "a"
    expected_output: ["abc", "array"]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (strings: List String) (pref: String) : List String :=
  strings.filter (fun s => s.startsWith pref)

def problem_spec
-- function signature
(implementation: List String → String → List String)
-- inputs
(strings: List String)
(pref: String) :=
-- spec
let spec (result: List String) :=
result.all (λ s => s.startsWith pref) ∧
result.all (λ s => s ∈ strings) ∧
strings.all (λ s => s.startsWith pref → s ∈ result) ∧
∀ s : String, s ∈ result → result.count s = strings.count s;
-- program termination
∃ result, implementation strings pref = result ∧
spec result

-- LLM HELPER
lemma filter_startsWith_all (strings : List String) (pref : String) :
  (strings.filter (fun s => s.startsWith pref)).all (fun s => s.startsWith pref) = true := by
  simp [List.all_eq_true]
  intros s hs
  have h := List.mem_filter.mp hs
  exact h.2

-- LLM HELPER
lemma filter_subset (strings : List String) (p : String → Bool) :
  (strings.filter p).all (fun s => s ∈ strings) = true := by
  simp [List.all_eq_true]
  intros s hs
  exact (List.mem_filter.mp hs).1

-- LLM HELPER
lemma filter_complete (strings : List String) (pref : String) :
  strings.all (fun s => s.startsWith pref → s ∈ strings.filter (fun s => s.startsWith pref)) = true := by
  simp [List.all_eq_true]
  intros s hs hstart
  exact List.mem_filter.mpr ⟨hs, hstart⟩

-- LLM HELPER
lemma filter_count_eq (strings : List String) (pref : String) (s : String) :
  s ∈ strings.filter (fun s => s.startsWith pref) →
  (strings.filter (fun s => s.startsWith pref)).count s = strings.count s := by
  intro h
  have h_starts : s.startsWith pref := (List.mem_filter.mp h).2
  rw [List.count_filter]
  simp [h_starts]

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref
:= by
  unfold problem_spec implementation
  use strings.filter (fun s => s.startsWith pref)
  simp
  constructor
  · exact filter_startsWith_all strings pref
  constructor  
  · exact filter_subset strings (fun s => s.startsWith pref)
  constructor
  · exact filter_complete strings pref
  · intros s hs
    exact filter_count_eq strings pref s hs

-- #test implementation [] "a" = []
-- #test implementation ["abc", "bcd", "cde", "array"] "a" = ["abc", "array"]