import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.isin: Element-wise test for membership in another array.

    Calculates `element in test_elements`, broadcasting over `element` only.
    Returns a boolean array of the same shape as `element` that is True
    where an element of `element` is in `test_elements` and False otherwise.

    This is an element-wise function version of the python keyword `in`.
    For 1-D arrays, this is roughly equivalent to:
    `np.array([item in test_elements for item in element])`
-/
def numpy_isin {n m : Nat} (element : Vector Float n) (test_elements : Vector Float m) : Id (Vector Bool n) :=
  sorry

/-- Specification: numpy.isin returns a boolean vector where each element indicates
    whether the corresponding element in the input vector is found in test_elements.

    Precondition: True (no special preconditions needed)
    Postcondition: For all indices i, result[i] = true iff element[i] is in test_elements
-/
theorem numpy_isin_spec {n m : Nat} (element : Vector Float n) (test_elements : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_isin element test_elements
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = true ↔ ∃ j : Fin m, element.get i = test_elements.get j⌝⦄ := by
  sorry