import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.divide: Divide arguments element-wise.

    Divides arguments element-wise. If the arrays have the same shape,
    each element of the result is the quotient of the corresponding elements
    from the input arrays.

    This is equivalent to x1 / x2 in terms of array broadcasting.
    Note: Division by zero will result in infinity or NaN depending on the numerator.
-/
def numpy_divide {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn fun i => x1.get i / x2.get i)

/-- Specification: numpy.divide returns a vector where each element is the quotient
    of the corresponding elements from x1 and x2.

    Precondition: All elements in x2 must be non-zero
    Postcondition: For all indices i, result[i] = x1[i] / x2[i]
-/
theorem numpy_divide_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜∀ i : Fin n, x2.get i ≠ 0⌝⦄
    numpy_divide x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i / x2.get i⌝⦄ := by
  simp [numpy_divide]
  intro h
  intro i
  simp [Vector.get_ofFn]