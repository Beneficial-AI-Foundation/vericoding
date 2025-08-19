import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(pref: String) :=
let spec (result: List String) :=
result.all (λ s => s.startsWith pref) ∧
result.all (λ s => s ∈ strings) ∧
strings.all (λ s => s.startsWith pref → s ∈ result) ∧
∀ s : String, s ∈ result → result.count s = strings.count s;
∃ result, implementation strings pref = result ∧
spec result

def implementation (strings: List String) (pref: String) : List String := 
  strings.filter (λ s => s.startsWith pref)

-- LLM HELPER
lemma filter_startsWith_all (strings: List String) (pref: String) :
  (strings.filter (λ s => s.startsWith pref)).all (λ s => s.startsWith pref) := by
  simp [List.all_filter]

-- LLM HELPER
lemma filter_mem_all (strings: List String) (pref: String) :
  (strings.filter (λ s => s.startsWith pref)).all (λ s => s ∈ strings) := by
  simp [List.all_def]
  intro s hs
  exact List.mem_of_mem_filter hs

-- LLM HELPER
lemma filter_preserves_all (strings: List String) (pref: String) :
  strings.all (λ s => s.startsWith pref → s ∈ strings.filter (λ s => s.startsWith pref)) := by
  simp [List.all_def]
  intro s hs hpref
  exact List.mem_filter.mpr ⟨hs, hpref⟩

-- LLM HELPER
lemma filter_count_eq (strings: List String) (pref: String) (s: String) :
  s ∈ strings.filter (λ s => s.startsWith pref) → 
  (strings.filter (λ s => s.startsWith pref)).count s = strings.count s := by
  intro h
  have h_mem : s ∈ strings := List.mem_of_mem_filter h
  have h_starts : s.startsWith pref := by
    rw [List.mem_filter] at h
    exact h.2
  rw [List.count_filter]
  simp [h_starts]

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref := by
  unfold problem_spec implementation
  use strings.filter (λ s => s.startsWith pref)
  constructor
  · rfl
  · constructor
    · exact filter_startsWith_all strings pref
    · constructor
      · exact filter_mem_all strings pref
      · constructor
        · exact filter_preserves_all strings pref
        · exact filter_count_eq strings pref