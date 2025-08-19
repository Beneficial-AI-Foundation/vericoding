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
lemma List.all_iff_forall {α : Type*} (p : α → Bool) (l : List α) : l.all p = true ↔ ∀ a ∈ l, p a = true := by
  simp [List.all_eq_true]

-- LLM HELPER
lemma List.mem_filter_iff {α : Type*} (p : α → Bool) (l : List α) (a : α) : a ∈ l.filter p ↔ a ∈ l ∧ p a = true := by
  simp [List.mem_filter]

-- LLM HELPER
lemma List.of_mem_filter {α : Type*} (p : α → Bool) (l : List α) (a : α) : a ∈ l.filter p → p a = true := by
  intro h
  exact (List.mem_filter_iff p l a).mp h |>.right

-- LLM HELPER
lemma List.mem_of_mem_filter {α : Type*} (p : α → Bool) (l : List α) (a : α) : a ∈ l.filter p → a ∈ l := by
  intro h
  exact (List.mem_filter_iff p l a).mp h |>.left

-- LLM HELPER
lemma List.mem_filter_of_mem {α : Type*} (p : α → Bool) (l : List α) (a : α) : a ∈ l → p a = true → a ∈ l.filter p := by
  intro h1 h2
  exact (List.mem_filter_iff p l a).mpr ⟨h1, h2⟩

-- LLM HELPER
lemma List.count_filter_eq {α : Type*} [DecidableEq α] (p : α → Bool) (l : List α) (a : α) : 
  (l.filter p).count a = if p a then l.count a else 0 := by
  simp [List.count_filter]

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref := by
  unfold problem_spec
  use strings.filter (λ s => s.startsWith pref)
  constructor
  · rfl
  · constructor
    · simp [List.all_iff_forall]
      intro s hs
      exact List.of_mem_filter _ _ _ hs
    · constructor
      · simp [List.all_iff_forall]
        intro s hs
        exact List.mem_of_mem_filter _ _ _ hs
      · constructor
        · simp [List.all_iff_forall]
          intro s hs hpref
          exact List.mem_filter_of_mem _ _ _ hs hpref
        · intro s hs
          have h_pref : s.startsWith pref = true := List.of_mem_filter _ _ _ hs
          simp [List.count_filter_eq]
          rw [if_pos h_pref]