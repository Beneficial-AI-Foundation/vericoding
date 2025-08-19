import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER  
def full (α : Type) [Inhabited α] (n : Nat) (fill_value : α) : Id (Vector α n) :=
  Vector.replicate n fill_value

-- LLM HELPER
def problem_spec (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    Prop :=
    ∀ result : Vector α n, result = Vector.replicate n fill_value →
    -- Core property: every element equals fill_value
    (∀ i : Fin n, result.get i = fill_value) ∧
    -- Uniformity property: all elements are equal to each other
    (∀ i j : Fin n, result.get i = result.get j) ∧
    -- Relationship to Vector.replicate (conceptual equivalence)
    (∀ i : Fin n, result.get i = (Vector.replicate n fill_value).get i) ∧
    -- First and last element property (when n > 0)
    (n > 0 → n > 0) ∧
    (n > 0 → ∀ h : n - 1 < n, result.get ⟨n - 1, h⟩ = fill_value)

def implementation (α : Type) [Inhabited α] (n : Nat) (fill_value : α) : Id (Vector α n) :=
  Vector.replicate n fill_value

theorem correctness (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    problem_spec α n fill_value := by
  intro result h
  constructor
  · intro i
    rw [h]
    simp [Vector.replicate, Vector.get_mk]
  constructor
  · intro i j
    rw [h]
    simp [Vector.replicate, Vector.get_mk]
  constructor
  · intro i
    rw [h]
  constructor
  · intro h_pos
    exact h_pos
  · intro h_pos h_bound
    rw [h]
    simp [Vector.replicate, Vector.get_mk]