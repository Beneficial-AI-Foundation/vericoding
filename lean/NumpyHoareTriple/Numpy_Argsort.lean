import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.argsort: Returns the indices that would sort an array.

    Returns an array of indices that would sort the input array in ascending order.
    These indices can be used to reorder the original array into sorted order.

    This function performs an indirect sort, returning indices rather than values.
-/
def numpy_argsort (a : Vector Float n) : Id (Vector (Fin n) n) :=
  sorry

/-- Specification: numpy.argsort returns indices that sort the array.

    Precondition: True
    Postcondition: Using the returned indices produces a sorted array
-/
theorem numpy_argsort_spec (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_argsort a
    ⦃⇓indices => ⌜∀ i j : Fin n, i < j → a.get (indices.get i) ≤ a.get (indices.get j)⌝⦄ := by
  sorry
