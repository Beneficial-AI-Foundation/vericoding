import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.nanargmin: Return the indices of the minimum values in the specified axis ignoring NaNs.
    
    For all-NaN slices ValueError is raised. Warning: the results cannot be trusted 
    if a slice contains only NaNs and Infs.
    
    This function finds the index of the minimum value in a vector, ignoring NaN values.
    If all values are NaN, it should raise an error (represented as a precondition).
    
    Parameters:
    - a : Vector Float n - Input data vector
    
    Returns:
    - Fin n - Index of the minimum non-NaN value
-/
def nanargmin {n : Nat} (a : Vector Float (n + 1)) (h_has_valid : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: nanargmin returns the index of the minimum non-NaN value.
    
    Precondition: At least one element in the vector is not NaN
    Postcondition: 
    1. The returned index points to a non-NaN value
    2. All non-NaN values at other indices are greater than or equal to the value at the returned index
    3. If there are ties, returns the first occurrence (smallest index)
-/
theorem nanargmin_spec {n : Nat} (a : Vector Float (n + 1)) (h_has_valid : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) :
    ⦃⌜∃ i : Fin (n + 1), ¬(a.get i).isNaN⌝⦄
    nanargmin a h_has_valid
    ⦃⇓idx => ⌜¬(a.get idx).isNaN ∧ 
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get idx ≤ a.get j) ∧
             (∀ j : Fin (n + 1), j < idx → (a.get j).isNaN ∨ a.get j > a.get idx)⌝⦄ := by
  sorry