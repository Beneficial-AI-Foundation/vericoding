/- 
{
  "name": "numpy.floor_divide",
  "description": "Return the largest integer smaller or equal to the division of the inputs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.floor_divide.html",
  "doc": "Return the largest integer smaller or equal to the division of the inputs.\n\nIt is equivalent to the Python // operator and pairs with the Python % (remainder), function so that a = a % b + b * (a // b) up to roundoff.",
}
-/

/-  numpy.floor_divide: Return the largest integer smaller or equal to the division of the inputs.

    Performs element-wise floor division of two vectors. For each pair of elements,
    returns the largest integer less than or equal to their division.

    This is equivalent to the Python // operator and pairs with the modulo operation
    such that a = a % b + b * (a // b) up to roundoff.
-/

/-  Specification: numpy.floor_divide returns a vector where each element is the floor
    of the division of the corresponding elements from x1 and x2.

    This function implements Python's // operator behavior for element-wise operations.

    Precondition: All elements in x2 must be non-zero
    Postcondition: 
    1. For all indices i, result[i] = floor(x1[i] / x2[i])
    2. For all indices i, result[i] is the largest integer ≤ x1[i] / x2[i]
    3. The fundamental floor division property: result[i] ≤ x1[i] / x2[i] < result[i] + 1
    4. This pairs with modulo such that: x1[i] = x2[i] * result[i] + remainder
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_floor_divide {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem numpy_floor_divide_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜∀ i : Fin n, x2.get i ≠ 0⌝⦄
    numpy_floor_divide x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, 
        result.get i = (x1.get i / x2.get i).floor ∧
        result.get i ≤ x1.get i / x2.get i ∧
        x1.get i / x2.get i < result.get i + 1⌝⦄ := by
  sorry
