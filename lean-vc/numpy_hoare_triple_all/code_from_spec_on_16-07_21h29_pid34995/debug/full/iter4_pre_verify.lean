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
  pure (Vector.replicate n fill_value)

-- LLM HELPER
lemma pos_of_gt_zero (n : Nat) (h : n > 0) : 0 < n := h

-- LLM HELPER
lemma wp_ret_of_pure {α : Type} (a : α) (P : α → Prop) :
    P a → ⦃⌜True⌝⦄ pure a ⦃⇓result => ⌜P result⌝⦄ := by
  intro h
  simp [pure]
  exact h

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
theorem full_spec (α : Type) [Inhabited α] [DecidableEq α] (n : Nat) (fill_value : α) :
    ⦃⌜True⌝⦄
    full α n fill_value
    ⦃⇓result => ⌜-- Core property: every element equals fill_value
                 (∀ i : Fin n, result.get i = fill_value) ∧
                 -- Uniformity property: all elements are equal to each other
                 (∀ i j : Fin n, result.get i = result.get j) ∧
                 -- Relationship to Vector.replicate (conceptual equivalence)
                 (∀ i : Fin n, result.get i = (Vector.replicate n fill_value).get i) ∧
                 -- First and last element property (when n > 0)
                 (n > 0 → result.get ⟨0, pos_of_gt_zero n⟩ = fill_value) ∧
                 (n > 0 → ∀ h : n - 1 < n, result.get ⟨n - 1, h⟩ = fill_value)⌝⦄ := by
  unfold full
  apply wp_ret_of_pure
  constructor
  · -- Core property: every element equals fill_value
    intro i
    exact Vector.get_replicate i fill_value
  constructor
  · -- Uniformity property: all elements are equal to each other
    intro i j
    simp [Vector.get_replicate]
  constructor
  · -- Relationship to Vector.replicate (conceptual equivalence)
    intro i
    rfl
  constructor
  · -- First element property (when n > 0)
    intro h
    exact Vector.get_replicate ⟨0, pos_of_gt_zero n h⟩ fill_value
  · -- Last element property (when n > 0)
    intro h h_bound
    exact Vector.get_replicate ⟨n - 1, h_bound⟩ fill_value