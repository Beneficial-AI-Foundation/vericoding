import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.minimum: Element-wise minimum of array elements.

    Compares two arrays element-wise and returns a new array containing
    the element-wise minima. If one of the elements being compared is NaN,
    then that element is returned.

    This is different from numpy.min which returns a single minimum value.
-/
def numpy_minimum {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  Id.pure (Vector.ofFn (fun i => min (x1.get i) (x2.get i)))

/-- Specification: numpy.minimum returns a vector where each element is the minimum
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for element-wise minimum)
    Postcondition: For all indices i, result[i] = min(x1[i], x2[i])
-/
theorem numpy_minimum_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_minimum x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = min (x1.get i) (x2.get i)⌝⦄ := by
  simp [numpy_minimum]
  rfl