import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.argmax: Returns the index of the maximum value in a vector.

    Returns the index of the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.
    
    In case of multiple occurrences of the maximum values, the indices
    corresponding to the first occurrence are returned.

    This function returns the position of the largest element in the array.
-/
def argmax {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: numpy.argmax returns the index of the maximum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the maximum value,
    and it is the first occurrence of such maximum value.
-/
theorem argmax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmax a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get j ≤ a.get i) ∧ 
            (∀ j : Fin (n + 1), a.get j = a.get i → i ≤ j)⌝⦄ := by
  sorry