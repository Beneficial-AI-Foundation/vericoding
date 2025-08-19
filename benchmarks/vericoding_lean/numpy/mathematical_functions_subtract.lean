import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.subtract",
  "description": "Subtract arguments, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.subtract.html",
  "doc": "Subtract arguments, element-wise.",
  "code": "# Universal function (ufunc) implemented in C\n# Binary operation: -\ndef subtract(x1, x2, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True):\n    '''Subtract arguments, element-wise'''\n    # Handle array conversion and broadcasting\n    x1 = np.asanyarray(x1)\n    x2 = np.asanyarray(x2)\n    \n    # Apply operation element-wise with broadcasting\n    # Uses optimized C loops for different data types\n    return _apply_ufunc(lambda a, b: a - b, x1, x2, out=out, where=where,\n                       casting=casting, order=order, dtype=dtype, subok=subok)"
}
-/

open Std.Do

/-- numpy.subtract: Subtract arguments, element-wise.

    Subtracts two vectors element-wise. If the vectors have the same shape,
    each element of the result is the difference of the corresponding elements
    from the input vectors.

    This is equivalent to x1 - x2 in terms of array broadcasting.
    The operation is the inverse of addition: (x1 - x2) + x2 = x1.
-/
def subtract {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: numpy.subtract returns a vector where each element is the difference
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for basic subtraction)
    Postcondition: For all indices i, result[i] = x1[i] - x2[i]
    
    Mathematical properties:
    - Subtraction is anti-commutative: x1 - x2 = -(x2 - x1)
    - Subtraction is the inverse of addition: (x1 - x2) + x2 = x1
    - Subtracting zero leaves the original value: x1 - 0 = x1
    - Subtracting a value from itself yields zero: x1 - x1 = 0
-/
theorem subtract_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    subtract x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i - x2.get i ∧
                  -- Sanity check: subtracting zero preserves the original value
                  (x2.get i = 0 → result.get i = x1.get i) ∧
                  -- Sanity check: subtracting a value from itself yields zero
                  (x1.get i = x2.get i → result.get i = 0) ∧
                  -- Anti-commutativity property can be verified
                  result.get i = -(x2.get i - x1.get i)⌝⦄ := by
  sorry