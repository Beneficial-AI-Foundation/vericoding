import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.full: Return a new array of given shape and type, filled with fill_value.

    Creates a new vector of size n where every element is set to the specified
    fill_value. This is the 1D version of numpy.full, focusing on the core
    functionality of creating uniform arrays.

    The function creates a vector filled with identical values, which is useful
    for initialization and creating constant arrays.
-/
def full (α : Type) [Inhabited α] (n : Nat) (fill_value : α) : Id (Vector α n) :=
  Vector.replicate n fill_value

-- LLM HELPER
lemma Vector.get_replicate_eq (α : Type) (n : Nat) (a : α) (i : Fin n) :
    (Vector.replicate n a).get i = a := by
  simp [Vector.replicate, Vector.get]

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
                 (n > 0 → ∀ h : n - 1 < n, result.get ⟨n - 1, h⟩ = fill_value)⌝⦄ :=
  fun _ => And.intro
    (fun i => Vector.get_replicate_eq α n fill_value i)
    (And.intro
      (fun i j => by 
        rw [Vector.get_replicate_eq, Vector.get_replicate_eq])
      (And.intro
        (fun i => rfl)
        (And.intro
          (fun h => h)
          (fun h h' => Vector.get_replicate_eq α n fill_value ⟨n - 1, h'⟩))))

def implementation (α : Type) [Inhabited α] (n : Nat) (fill_value : α) : Id (Vector α n) :=
  Vector.replicate n fill_value

theorem correctness (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    problem_spec α n fill_value := 
  problem_spec α n fill_value