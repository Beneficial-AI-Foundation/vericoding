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
    cases h_aux : find_longest_aux tail (idx + 1) with
    | none => 
      simp [h_aux] at h
      exact Or.inl h
    | some longest =>
      simp [h_aux] at h
      by_cases h_cond : head.length > longest.length
      · simp [h_cond] at h
        exact Or.inl h
      · simp [h_cond] at h
        exact Or.inr (ih s h_aux)

-- LLM HELPER
lemma find_longest_aux_maximal (strings: List String) (idx: Nat) :
  ∀ s longest, find_longest_aux strings idx = some longest → 
  s ∈ strings → s.length ≤ longest.length := by
  induction strings with
  | nil => simp [find_longest_aux]
  | cons head tail ih =>
    intro s longest h hs
    simp [find_longest_aux] at h
    cases h_aux : find_longest_aux tail (idx + 1) with
    | none =>
      simp [h_aux] at h
      cases hs with
      | inl h_eq => 
        simp [h_eq, h]
      | inr h_mem =>
        exfalso
        have : tail = [] := by
          cases tail with
          | nil => rfl
          | cons _ _ => simp [find_longest_aux] at h_aux
        simp [this] at h_mem
    | some aux_longest =>
      simp [h_aux] at h
      cases hs with
      | inl h_eq =>
        simp [h_eq]
        by_cases h_cond : head.length > aux_longest.length
        · simp [h_cond] at h
          simp [h]
        · simp [h_cond] at h
          simp [h]
          exact Nat.le_trans (Nat.le_refl _) (Nat.le_of_not_gt h_cond)
      | inr h_mem =>
        by_cases h_cond : head.length > aux_longest.length
        · simp [h_cond] at h
          simp [h]
          exact Nat.le_trans (ih s aux_longest h_aux h_mem) (Nat.le_of_lt h_cond)
        · simp [h_cond] at h
          simp [h]
          exact ih s aux_longest h_aux h_mem

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
    cases h_aux : find_longest_aux tail 1 with
    | none =>
      use head
      simp
      constructor
      · simp [h]
      · intro s hs hlen
        simp [h] at hs
        cases hs with
        | inl h_eq => simp [h_eq]
        | inr h_mem => 
          have : tail = [] := by
            cases tail with
            | nil => rfl
            | cons _ _ => simp [find_longest_aux] at h_aux
          simp [this] at h_mem
    | some aux_longest =>
      by_cases h_cond : head.length > aux_longest.length
      · simp [h_cond, h_aux]
        use head
        constructor
        · simp [h]
        · intro s hs hlen
          simp [h] at hs
          cases hs with
          | inl h_eq => simp [h_eq]
          | inr h_mem =>
            have : s.length ≤ aux_longest.length := 
              find_longest_aux_maximal tail 1 s aux_longest h_aux h_mem
            exact Nat.le_trans this (Nat.le_of_lt h_cond)
      · simp [h_cond, h_aux]
        use aux_longest
        constructor
        · right
          exact find_longest_aux_mem tail 1 aux_longest h_aux
        · intro s hs hlen
          simp [h] at hs
          cases hs with
          | inl h_eq =>
            simp [h_eq]
            exact Nat.le_of_not_gt h_cond
          | inr h_mem =>
            exact find_longest_aux_maximal tail 1 s aux_longest h_aux h_mem