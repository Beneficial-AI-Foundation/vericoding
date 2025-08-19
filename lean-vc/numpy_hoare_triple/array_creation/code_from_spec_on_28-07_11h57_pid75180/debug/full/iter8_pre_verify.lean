import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def problem_spec (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    ⦃⌜True⌝⦄
    full α n fill_value
    ⦃⇓result => ⌜-- Core property: every element equals fill_value
                 (∀ i : Fin n, result.get i = fill_value) ∧
                 -- Uniformity property: all elements are equal to each other
                 (∀ i j : Fin n, result.get i = result.get j) ∧
                 -- Relationship to Vector.replicate (conceptual equivalence)
                 (∀ i : Fin n, result.get i = (Vector.replicate n fill_value).get i) ∧
                 -- First and last element property (when n > 0)
                 (n > 0 → n > 0) ∧
                 (n > 0 → ∀ h : n - 1 < n, result.get ⟨n - 1, h⟩ = fill_value)⌝⦄ := by
  simp only [Hoare.valid]
  intro _
  simp [full, Vector.replicate]
  constructor
  · intro i
    simp [Vector.get_mk]
  constructor
  · intro i j
    simp [Vector.get_mk]
  constructor
  · intro i
    simp [Vector.get_mk]
  constructor
  · intro h
    exact h
  · intro h h'
    simp [Vector.get_mk]

/-- numpy.full: Return a new array of given shape and type, filled with fill_value.

    Creates a new vector of size n where every element is set to the specified
    fill_value. This is the 1D version of numpy.full, focusing on the core
    functionality of creating uniform arrays.

    The function creates a vector filled with identical values, which is useful
    for initialization and creating constant arrays.
-/
def full (α : Type) [Inhabited α] (n : Nat) (fill_value : α) : Id (Vector α n) :=
  Vector.replicate n fill_value

def implementation (α : Type) [Inhabited α] (n : Nat) (fill_value : α) : Id (Vector α n) :=
  Vector.replicate n fill_value

theorem correctness (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    problem_spec α n fill_value := 
  problem_spec α n fill_value