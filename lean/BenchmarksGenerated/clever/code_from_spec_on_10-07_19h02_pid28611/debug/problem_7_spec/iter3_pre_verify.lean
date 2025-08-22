import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(substring: String) :=
let spec (result: List String) :=
(∀ i, i < result.length → result[i]!.containsSubstr substring.toSubstring = true) ∧
(∀ s, s ∈ result → s ∈ strings ∧ s.containsSubstr substring.toSubstring = true) ∧
(∀ s, s ∈ strings → s.containsSubstr substring.toSubstring = true → s ∈ result) ∧
(∀ s, s ∈ result → result.count s = strings.count s);
∃ result, implementation strings substring = result ∧
spec result

def implementation (strings: List String) (substring: String): List String := 
  strings.filter (fun s => s.containsSubstr substring.toSubstring)

-- LLM HELPER
lemma mem_filter_iff (p : α → Bool) (a : α) (l : List α) : 
  a ∈ l.filter p ↔ a ∈ l ∧ p a = true := by
  simp [List.mem_filter]

-- LLM HELPER
lemma get_filter_mem (p : α → Bool) (l : List α) (i : Nat) (h : i < (l.filter p).length) :
  (l.filter p)[i]! ∈ l := by
  have : (l.filter p)[i]! ∈ l.filter p := List.getElem_mem (l.filter p) i h
  rw [mem_filter_iff] at this
  exact this.1

-- LLM HELPER
lemma get_filter_prop (p : α → Bool) (l : List α) (i : Nat) (h : i < (l.filter p).length) :
  p ((l.filter p)[i]!) = true := by
  have : (l.filter p)[i]! ∈ l.filter p := List.getElem_mem (l.filter p) i h
  rw [mem_filter_iff] at this
  exact this.2

-- LLM HELPER
lemma count_filter_eq [BEq α] (p : α → Bool) (l : List α) (a : α) :
  (l.filter p).count a = if p a then l.count a else 0 := by
  simp [List.count_filter]

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring := by
  unfold problem_spec implementation
  use strings.filter (fun s => s.containsSubstr substring.toSubstring)
  constructor
  · rfl
  · constructor
    · intro i hi
      exact get_filter_prop (fun s => s.containsSubstr substring.toSubstring) strings i hi
    · constructor
      · intro s hs
        rw [mem_filter_iff] at hs
        exact hs
      · constructor
        · intro s hs hcontains
          rw [mem_filter_iff]
          exact ⟨hs, hcontains⟩
        · intro s hs
          rw [mem_filter_iff] at hs
          rw [count_filter_eq]
          simp [hs.2]