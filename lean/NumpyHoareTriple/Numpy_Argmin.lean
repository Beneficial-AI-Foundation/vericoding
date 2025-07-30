import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.argmin: Returns the index of the minimum value.

    Returns the index of the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This function returns the position of the smallest element in the array.
-/
def numpy_argmin (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: numpy.argmin returns the index of the minimum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the minimum value
-/
theorem numpy_argmin_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmin a
    ⦃⇓i => ⌜∀ j : Fin (n + 1), a.get i ≤ a.get j⌝⦄ := by
  sorry
