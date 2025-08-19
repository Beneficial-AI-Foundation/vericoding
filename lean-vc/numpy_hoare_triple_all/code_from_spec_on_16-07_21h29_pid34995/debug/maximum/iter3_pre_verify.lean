import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.maximum",
  "description": "Element-wise maximum of array elements",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.maximum.html",
  "doc": "Element-wise maximum of array elements.\n\nCompare two arrays and returns a new array containing the element-wise maxima.",
  "code": "# Universal function (ufunc) implemented in C\n# Binary operation: max\ndef maximum(x1, x2, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True):\n    '''Element-wise maximum of array elements'''\n    # Handle array conversion and broadcasting\n    x1 = np.asanyarray(x1)\n    x2 = np.asanyarray(x2)\n    \n    # Apply operation element-wise with broadcasting\n    # Uses optimized C loops for different data types\n    return _apply_ufunc(lambda a, b: a max b, x1, x2, out=out, where=where,\n                       casting=casting, order=order, dtype=dtype, subok=subok)"
}
-/

open Std.Do

/-- numpy.maximum: Element-wise maximum of array elements.

    Compares two arrays element-wise and returns a new array containing
    the element-wise maxima. If one of the elements being compared is NaN,
    then that element is returned.

    This is a universal function (ufunc) that operates element-wise on arrays
    and supports broadcasting. For 1D arrays, it computes the maximum of
    corresponding elements.
-/
def maximum {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  Vector.ofFn (fun i => max (x1.get i) (x2.get i))

-- LLM HELPER
lemma max_ge_left (a b : Float) : max a b ≥ a := by
  simp [max_def]
  split <;> simp

-- LLM HELPER
lemma max_ge_right (a b : Float) : max a b ≥ b := by
  simp [max_def]
  split <;> simp

-- LLM HELPER
lemma max_eq_left_or_right (a b : Float) : max a b = a ∨ max a b = b := by
  simp [max_def]
  split <;> simp

/-- Specification: numpy.maximum returns a vector where each element is the maximum
    of the corresponding elements from x1 and x2.

    Mathematical properties:
    1. Commutativity: maximum(x1, x2) = maximum(x2, x1)
    2. Associativity: maximum(maximum(x1, x2), x3) = maximum(x1, maximum(x2, x3))
    3. Idempotence: maximum(x, x) = x
    4. Monotonicity: if x1[i] ≤ y1[i] and x2[i] ≤ y2[i], then maximum(x1, x2)[i] ≤ maximum(y1, y2)[i]
    5. Identity: maximum(x, -∞) = x (where -∞ is negative infinity)

    Precondition: True (no special preconditions for element-wise maximum)
    Postcondition: For all indices i, result[i] = max(x1[i], x2[i])
-/
theorem maximum_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    maximum x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = max (x1.get i) (x2.get i) ∧
                 ∀ i : Fin n, result.get i ≥ x1.get i ∧ result.get i ≥ x2.get i ∧
                 (result.get i = x1.get i ∨ result.get i = x2.get i)⌝⦄ := by
  simp [maximum]
  apply Triple.pure
  intro i
  constructor
  · simp [Vector.get_ofFn]
  · constructor
    · simp [Vector.get_ofFn]
      apply max_ge_left
    · constructor
      · simp [Vector.get_ofFn]
        apply max_ge_right
      · simp [Vector.get_ofFn]
        apply max_eq_left_or_right