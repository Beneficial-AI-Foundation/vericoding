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
(∀ i, i < result.length → result[i]!.containsSubstr substring →
∀ j, j < strings.length ∧ strings[j]!.containsSubstr substring → strings[j]! ∈ result →
∀ j, j < result.length → result.count result[j]! = strings.count result[j]!);
∃ result, implementation strings substring = result ∧
spec result

def implementation (strings: List String) (substring: String): List String := 
  strings.filter (fun s => s.containsSubstr substring)

-- LLM HELPER
lemma mem_filter_iff (p : α → Bool) (a : α) (l : List α) : 
  a ∈ l.filter p ↔ a ∈ l ∧ p a := by
  simp [List.mem_filter]

-- LLM HELPER
lemma length_filter_le (p : α → Bool) (l : List α) : 
  (l.filter p).length ≤ l.length := by
  simp [List.length_filter_le]

-- LLM HELPER
lemma get_filter_mem (p : α → Bool) (l : List α) (i : Nat) (h : i < (l.filter p).length) :
  (l.filter p)[i] ∈ l := by
  have : (l.filter p)[i] ∈ l.filter p := List.get_mem (l.filter p) i h
  rw [mem_filter_iff] at this
  exact this.1

-- LLM HELPER
lemma get_filter_prop (p : α → Bool) (l : List α) (i : Nat) (h : i < (l.filter p).length) :
  p ((l.filter p)[i]) = true := by
  have : (l.filter p)[i] ∈ l.filter p := List.get_mem (l.filter p) i h
  rw [mem_filter_iff] at this
  exact this.2

-- LLM HELPER
lemma count_filter_eq (p : α → Bool) (l : List α) (a : α) :
  (l.filter p).count a = if p a then l.count a else 0 := by
  simp [List.count_filter]

theorem correctness
(strings: List String)
(substring: String)
: problem_spec implementation strings substring := by
  unfold problem_spec implementation
  use strings.filter (fun s => s.containsSubstr substring)
  constructor
  · rfl
  · intro i hi hcontains j hj hmem k hk
    simp [List.get_eq_getElem] at hcontains
    have hget_mem : (strings.filter (fun s => s.containsSubstr substring))[i] ∈ strings := 
      get_filter_mem (fun s => s.containsSubstr substring) strings i hi
    have hget_prop : (strings.filter (fun s => s.containsSubstr substring))[i].containsSubstr substring := 
      get_filter_prop (fun s => s.containsSubstr substring) strings i hi
    rw [count_filter_eq, count_filter_eq]
    have result_k_mem : (strings.filter (fun s => s.containsSubstr substring))[k] ∈ strings.filter (fun s => s.containsSubstr substring) :=
      List.get_mem _ k hk
    rw [mem_filter_iff] at result_k_mem
    simp [result_k_mem.2]