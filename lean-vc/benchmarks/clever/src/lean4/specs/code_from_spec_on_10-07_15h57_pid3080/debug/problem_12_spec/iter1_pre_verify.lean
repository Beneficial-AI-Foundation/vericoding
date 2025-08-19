import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List String → Option String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: Option String) :=
  (result = none ↔ strings.length = 0) ∨
  (∃ longest, result = some longest ∧
  longest ∈ strings ∧
  ∀ s, s ∈ strings → s.length ≤ longest.length →
  (∃ i, i < strings.length ∧
  strings[i]! = longest ∧ ∀ j < i, strings[j]!.length < longest.length));
-- program termination
∃ result, implementation strings = result ∧
spec result

-- LLM HELPER
def find_longest_aux (strings: List String) (idx: Nat) : Option String :=
  match strings with
  | [] => none
  | s :: rest =>
    match find_longest_aux rest (idx + 1) with
    | none => some s
    | some longest =>
      if s.length > longest.length then some s else some longest

def implementation (strings: List String) : Option String := 
  match strings with
  | [] => none
  | s :: rest =>
    match find_longest_aux rest 1 with
    | none => some s
    | some longest => 
      if s.length > longest.length then some s else some longest

-- LLM HELPER
lemma find_longest_aux_mem (strings: List String) (idx: Nat) :
  ∀ s, find_longest_aux strings idx = some s → s ∈ strings := by
  induction strings with
  | nil => simp [find_longest_aux]
  | cons head tail ih =>
    intro s h
    simp [find_longest_aux] at h
    split at h
    · split at h
      · simp at h
        simp [h]
      · simp at h
        split at h
        · simp [h]
        · right
          exact ih s h
    · right
      exact ih s h

-- LLM HELPER
lemma find_longest_aux_maximal (strings: List String) (idx: Nat) :
  ∀ s longest, find_longest_aux strings idx = some longest → 
  s ∈ strings → s.length ≤ longest.length := by
  induction strings with
  | nil => simp [find_longest_aux]
  | cons head tail ih =>
    intro s longest h hs
    simp [find_longest_aux] at h
    simp at hs
    cases hs with
    | inl h_eq =>
      simp [h_eq]
      split at h
      · simp at h
        simp [h]
      · split at h
        · simp at h
          simp [h]
        · simp at h
          split at h
          · simp [h]
          · have := ih s _ h (by simp)
            simp at this
            exact this
    | inr h_mem =>
      split at h
      · simp at h
        simp [h]
        exact ih s head (by simp) h_mem
      · split at h
        · simp at h
          simp [h]
          exact ih s head (by simp) h_mem
        · simp at h
          exact ih s longest h h_mem

theorem correctness
(strings: List String)
: problem_spec implementation strings
:= by
  unfold problem_spec
  simp
  cases h : strings with
  | nil =>
    simp [implementation]
    left
    simp [h]
  | cons head tail =>
    simp [implementation]
    right
    split
    · simp
      use head
      simp
      constructor
      · simp [h]
      · intro s hs hlen
        simp [h] at hs
        cases hs with
        | inl h_eq => simp [h_eq]
        | inr h_mem => 
          have : find_longest_aux tail 1 = none := by assumption
          simp [find_longest_aux] at this
          cases tail with
          | nil => simp at h_mem
          | cons _ _ => simp at this
    · rename_i longest h_some
      use longest
      constructor
      · split
        · simp
          have : find_longest_aux tail 1 = some longest := h_some
          exact find_longest_aux_mem tail 1 longest this
        · simp
          simp [h]
      · constructor
        · split
          · simp
            have : find_longest_aux tail 1 = some longest := h_some
            right
            exact find_longest_aux_mem tail 1 longest this
          · simp [h]
        · intro s hs hlen
          simp [h] at hs
          cases hs with
          | inl h_eq =>
            simp [h_eq]
            split at *
            · simp at hlen
            · exact le_refl _
          | inr h_mem =>
            split at *
            · simp
              have : find_longest_aux tail 1 = some longest := h_some
              exact find_longest_aux_maximal tail 1 s longest this h_mem
            · simp
              have : find_longest_aux tail 1 = some longest := h_some
              exact find_longest_aux_maximal tail 1 s longest this h_mem