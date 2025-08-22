import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.reshape: Gives a new shape to an array without changing its data.

    For 1D arrays, reshape can only produce shapes with the same total
    number of elements. The most common 1D reshape operations are:
    - Reshape to a different 1D shape (must have same size)
    - Special case: -1 in shape means "infer this dimension"

    This simplified version handles 1D to 1D reshaping only.
-/
def numpy_reshape {n m : Nat} (a : Vector Float n) (h_size : n = m) : Id (Vector Float m) :=
  sorry

/-- Specification: numpy.reshape returns a vector with new shape but same elements.

    Precondition: The new shape must have the same total number of elements
    Postcondition: Elements appear in the same order in the reshaped array
-/
theorem numpy_reshape_spec {n m : Nat} (a : Vector Float n) (h_size : n = m) :
    ⦃⌜n = m⌝⦄
    numpy_reshape a h_size
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = a.get (i.cast h_size.symm)⌝⦄ := by
  sorry
