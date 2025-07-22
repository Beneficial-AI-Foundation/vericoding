import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.prod: Product of array elements.

    Returns the product of all elements in the array. For empty arrays,
    returns 1 as the identity element of multiplication.

    This is a reduction operation that multiplies all values in the
    array into a single scalar result.
-/
def numpy_prod {n : Nat} (a : Vector Float n) : Id Float :=
  pure (a.toList.foldl (· * ·) 1)

/-- Specification: numpy.prod returns the product of all elements in the vector.

    Precondition: True (works for any vector, including empty)
    Postcondition: result = product of all elements (1 for empty vector)
-/
theorem numpy_prod_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_prod a
    ⦃⇓result => ⌜result = (a.toList.foldl (· * ·) 1)⌝⦄ := by
  simp [numpy_prod]
  apply Triple.pure
  rfl