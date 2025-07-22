import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.sum: Sum of array elements.

    Returns the sum of all elements in the array. For empty arrays,
    returns 0 as the identity element of addition.

    This is a reduction operation that aggregates all values in the
    array into a single scalar result.
-/
def numpy_sum {n : Nat} (a : Vector Float n) : Id Float :=
  pure (List.sum (a.toList))

/-- Specification: numpy.sum returns the sum of all elements in the vector.

    Precondition: True (works for any vector, including empty)
    Postcondition: result = sum of all elements (0 for empty vector)
-/
theorem numpy_sum_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_sum a
    ⦃⇓result => ⌜result = (List.sum (a.toList))⌝⦄ := by
  simp [numpy_sum]
  apply Triple.ret