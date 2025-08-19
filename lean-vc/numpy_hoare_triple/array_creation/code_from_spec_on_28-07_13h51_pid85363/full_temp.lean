import Std.Do.Triple
import Std.Tactic.Do

def full_spec (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) : Prop :=
  ∀ result : Vector α n,
    result = full α n fill_value →
    -- Core property: every element equals fill_value
    (∀ i : Fin n, result.get i = fill_value) ∧
    -- Uniformity property: all elements are equal to each other
    (∀ i j : Fin n, result.get i = result.get j) ∧
    -- Relationship to Vector.replicate (conceptual equivalence)
    (∀ i : Fin n, result.get i = (Vector.replicate n fill_value).get i) ∧
    -- First and last element property (when n > 0)
    (n > 0 → result.get ⟨0, Nat.zero_lt_of_ne_zero (Nat.pos_iff_ne_zero.mp ‹n > 0›)⟩ = fill_value) ∧
    (n > 0 → ∀ h : n - 1 < n, result.get ⟨n - 1, h⟩ = fill_value)

def problem_spec := full_spec

open Std.Do

/-- numpy.full: Return a new array of given shape and type, filled with fill_value.

    Creates a new vector of size n where every element is set to the specified
    fill_value. This is the 1D version of numpy.full, focusing on the core
    functionality of creating uniform arrays.

    The function creates a vector filled with identical values, which is useful
    for initialization and creating constant arrays.
-/
def full (α : Type) [Inhabited α] (n : Nat) (fill_value : α) : Vector α n :=
  Vector.replicate n fill_value

-- LLM HELPER
lemma Vector.get_replicate (α : Type) (n : Nat) (val : α) (i : Fin n) :
    (Vector.replicate n val).get i = val := by
  simp [Vector.replicate, Vector.get]

theorem correctness (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    full_spec α n fill_value := by
  intro result h_eq
  rw [h_eq]
  constructor
  · intro i
    simp [full, Vector.get_replicate]
  constructor
  · intro i j
    simp [full, Vector.get_replicate]
  constructor
  · intro i
    rfl
  constructor
  · intro h
    simp [full, Vector.get_replicate]
  · intro h h_bound
    simp [full, Vector.get_replicate]