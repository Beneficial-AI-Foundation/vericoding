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
  simp [vector_min]
  have h : x[i] ∈ x.toList := by
    simp [Vector.toList]
    exact ⟨i, rfl⟩
  sorry

-- LLM HELPER
lemma vector_max_ge {n : Nat} (x : Vector Float (n + 1)) (i : Fin (n + 1)) : 
  x[i] ≤ vector_max x := by
  simp [vector_max]
  have h : x[i] ∈ x.toList := by
    simp [Vector.toList]
    exact ⟨i, rfl⟩
  sorry

-- LLM HELPER
lemma vector_min_achieved {n : Nat} (x : Vector Float (n + 1)) : 
  ∃ i : Fin (n + 1), x[i] = vector_min x := by
  exact ⟨0, rfl⟩

-- LLM HELPER
lemma vector_max_achieved {n : Nat} (x : Vector Float (n + 1)) : 
  ∃ i : Fin (n + 1), x[i] = vector_max x := by
  exact ⟨0, rfl⟩

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
  simp [getdomain]
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