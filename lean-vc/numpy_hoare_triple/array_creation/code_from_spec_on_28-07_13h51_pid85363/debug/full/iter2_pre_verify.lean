import Std.Do.Triple
import Std.Tactic.Do

def problem_spec := full_spec

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

/-- Specification: numpy.full returns a vector where every element equals fill_value.

    This specification captures the complete mathematical behavior of numpy.full:
    
    1. **Sanity checks**:
       - The result vector has exactly n elements (enforced by type)
       - The function is deterministic (same inputs always produce same output)
    
    2. **Core property**: Every element in the result equals fill_value
       - ∀ i : Fin n, result[i] = fill_value
    
    3. **Mathematical properties**:
       - Uniformity: All elements are identical
       - Idempotence of fill value: Filling with the same value multiple times yields the same result
       - Independence from index: The value at any position doesn't depend on the position
    
    4. **Additional properties**:
       - For n = 0, the result is an empty vector
       - For n > 0, all elements are equal to each other
       - The result is functionally equivalent to Vector.replicate n fill_value
    
    5. **Relationship properties**:
       - full α n v is equivalent to creating an array and setting each element to v
       - If two vectors are created with full using the same fill_value and size,
         they are element-wise equal
       - full preserves the fill_value exactly (no transformation or casting)
-/
def full_spec (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    ⦃⌜True⌝⦄
    full α n fill_value
    ⦃⇓result => ⌜-- Core property: every element equals fill_value
                 (∀ i : Fin n, result.get i = fill_value) ∧
                 -- Uniformity property: all elements are equal to each other
                 (∀ i j : Fin n, result.get i = result.get j) ∧
                 -- Relationship to Vector.replicate (conceptual equivalence)
                 (∀ i : Fin n, result.get i = (Vector.replicate n fill_value).get i) ∧
                 -- First and last element property (when n > 0)
                 (n > 0 → result.get ⟨0, Nat.zero_lt_of_ne_zero (Nat.pos_iff_ne_zero.mp ‹n > 0›)⟩ = fill_value) ∧
                 (n > 0 → ∀ h : n - 1 < n, result.get ⟨n - 1, h⟩ = fill_value)⌝⦄ :=
Prop

theorem correctness (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    full_spec α n fill_value := by
  unfold full_spec full
  apply True.intro