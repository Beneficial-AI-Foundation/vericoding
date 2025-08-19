import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def vector_min {n : Nat} (x : Vector Float (n + 1)) : Float :=
  x.toList.foldl min (x.get 0)

-- LLM HELPER
def vector_max {n : Nat} (x : Vector Float (n + 1)) : Float :=
  x.toList.foldl max (x.get 0)

-- LLM HELPER
lemma vector_min_le {n : Nat} (x : Vector Float (n + 1)) (i : Fin (n + 1)) : 
  vector_min x ≤ x[i] := by
  unfold vector_min
  have h : x[i] ∈ x.toList := by
    simp [Vector.toList]
    exact ⟨i, rfl⟩
  induction x.toList generalizing x[i] with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.foldl]
    by_cases h' : head = x[i]
    · simp [h']
    · have : x[i] ∈ tail := by
        simp [List.mem_cons] at h
        exact h.resolve_left h'
      exact le_trans (min_le_right _ _) (ih this)

-- LLM HELPER
lemma vector_max_ge {n : Nat} (x : Vector Float (n + 1)) (i : Fin (n + 1)) : 
  x[i] ≤ vector_max x := by
  unfold vector_max
  have h : x[i] ∈ x.toList := by
    simp [Vector.toList]
    exact ⟨i, rfl⟩
  induction x.toList generalizing x[i] with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.foldl]
    by_cases h' : head = x[i]
    · simp [h']
    · have : x[i] ∈ tail := by
        simp [List.mem_cons] at h
        exact h.resolve_left h'
      exact le_trans (ih this) (le_max_right _ _)

-- LLM HELPER
lemma vector_min_achieved {n : Nat} (x : Vector Float (n + 1)) : 
  ∃ i : Fin (n + 1), x[i] = vector_min x := by
  use 0
  unfold vector_min
  simp [Vector.get, Vector.toList]
  rfl

-- LLM HELPER
lemma vector_max_achieved {n : Nat} (x : Vector Float (n + 1)) : 
  ∃ i : Fin (n + 1), x[i] = vector_max x := by
  use 0
  unfold vector_max
  simp [Vector.get, Vector.toList]
  rfl

-- LLM HELPER
lemma vector_min_le_max {n : Nat} (x : Vector Float (n + 1)) : 
  vector_min x ≤ vector_max x := by
  have h := vector_min_le x 0
  have h2 := vector_max_ge x 0
  exact le_trans h h2

def getdomain {n : Nat} (x : Vector Float (n + 1)) : Id (Vector Float 2) :=
  return ⟨#[vector_min x, vector_max x], rfl⟩

theorem getdomain_spec {n : Nat} (x : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    getdomain x
    ⦃⇓result => ⌜
      result[0] ≤ result[1] ∧
      (∀ i : Fin (n + 1), result[0] ≤ x[i] ∧ x[i] ≤ result[1]) ∧
      (∃ i : Fin (n + 1), x[i] = result[0]) ∧
      (∃ j : Fin (n + 1), x[j] = result[1])
    ⌝⦄ := by
  unfold getdomain
  unfold ht
  simp
  constructor
  · exact vector_min_le_max x
  constructor
  · intro i
    constructor
    · exact vector_min_le x i
    · exact vector_max_ge x i
  constructor
  · exact vector_min_achieved x
  · exact vector_max_achieved x