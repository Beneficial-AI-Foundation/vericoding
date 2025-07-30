import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.argmax: Returns the index of the maximum value.

    Returns the index of the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.

    This function returns the position of the largest element in the array.
-/
def numpy_argmax (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry

/-- Specification: numpy.argmax returns the index of the maximum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the maximum value
-/
theorem numpy_argmax_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmax a
    ⦃⇓i => ⌜∀ j : Fin (n + 1), a.get j ≤ a.get i⌝⦄ := by
  sorry
