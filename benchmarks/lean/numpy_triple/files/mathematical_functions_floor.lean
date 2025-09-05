/- 
{
  "name": "numpy.floor",
  "description": "Return the floor of the input, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.floor.html",
  "doc": "Return the floor of the input, element-wise.\n\nThe floor of the scalar x is the largest integer i, such that i <= x.",
}
-/

/-  numpy.floor: Return the floor of the input, element-wise.

    The floor of each element x is the largest integer i, such that i <= x.
    This is a fundamental mathematical operation that rounds down to the
    nearest integer.

    Returns an array of the same shape as x, containing the floor of each element.
-/

/-  Specification: numpy.floor returns a vector where each element is the
    floor (largest integer less than or equal to) the corresponding element in x.

    Precondition: True (floor is defined for all real numbers)
    Postcondition: For all indices i, result[i] is the floor of x[i], meaning:
    - result[i] is an integer value (represented as Float)
    - result[i] ≤ x[i]
    - x[i] < result[i] + 1
    - There is no integer k such that result[i] < k ≤ x[i]
    - Monotonicity: if x[i] ≤ x[j] then result[i] ≤ result[j]
    - Idempotence: floor(floor(x)) = floor(x)
    - Relationship with ceiling: result[i] = -((-x[i]).ceil) when x[i] is not an integer
    - Integer preservation: if x[i] is an integer, then result[i] = x[i]
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_floor {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem numpy_floor_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_floor x
    ⦃⇓result => ⌜∀ i : Fin n,
      (∃ k : Int, result.get i = Float.ofInt k) ∧
      result.get i ≤ x.get i ∧
      x.get i < result.get i + 1 ∧
      (∀ k : Int, Float.ofInt k ≤ x.get i → Float.ofInt k ≤ result.get i) ∧
      (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j) ∧
      (∃ k : Int, result.get i = Float.ofInt k → (result.get i).floor = result.get i) ∧
      result.get i = -((-x.get i).ceil) ∧
      (∃ k : Int, x.get i = Float.ofInt k → result.get i = x.get i)⌝⦄ := by
  sorry
