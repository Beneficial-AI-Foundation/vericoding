import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
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
  rw [List.all_eq_true]
  intro s h
  rw [List.mem_filter] at h
  exact h.2

-- LLM HELPER
lemma filter_mem_all (strings: List String) (pref: String) :
  (strings.filter (λ s => s.startsWith pref)).all (λ s => s ∈ strings) := by
  rw [List.all_eq_true]
  intro s h
  rw [List.mem_filter] at h
  exact h.1

-- LLM HELPER
lemma strings_startsWith_in_filter (strings: List String) (pref: String) :
  strings.all (λ s => s.startsWith pref → s ∈ strings.filter (λ s => s.startsWith pref)) := by
  rw [List.all_eq_true]
  intro s h_mem
  intro h_starts
  rw [List.mem_filter]
  exact ⟨h_mem, h_starts⟩

-- LLM HELPER
lemma filter_count_eq (strings: List String) (pref: String) :
  ∀ s : String, s ∈ strings.filter (λ s => s.startsWith pref) → 
  (strings.filter (λ s => s.startsWith pref)).count s = strings.count s := by
  intro s h_mem
  rw [List.count_filter]
  rw [List.mem_filter] at h_mem
  have h_starts : s.startsWith pref := h_mem.2
  simp only [h_starts, decide_True, Bool.true_and]

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref := by
  use strings.filter (λ s => s.startsWith pref)
  constructor
  · rfl
  · constructor
    · exact filter_startsWith_all strings pref
    · constructor
      · exact filter_mem_all strings pref
      · constructor
        · exact strings_startsWith_in_filter strings pref
        · exact filter_count_eq strings pref