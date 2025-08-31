/- 
{
  "name": "numpy.exp2",
  "description": "Calculate 2**p for all p in the input array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.exp2.html",
  "doc": "Calculate 2**p for all p in the input array.",
}
-/

/-  numpy.exp2: Calculate 2 raised to the power of each element in the input vector.

    Computes 2^p for all p in the input vector, element-wise.
    This is equivalent to applying the exponential function with base 2
    to each element of the input vector.

    From NumPy documentation:
    - Parameters: x (array_like) - Input values
    - Returns: y (ndarray) - 2**x, element-wise
    
    The function is implemented as a universal function (ufunc) that
    operates element-wise on arrays and supports broadcasting.
    For finite input values, the result is always positive.
-/

/-  Specification: numpy.exp2 computes 2 raised to the power of each element 
    in the input vector.

    Mathematical Properties:
    1. Element-wise correctness: result[i] = 2^x[i] for all i
    2. Fundamental exponential identity: exp2(0) = 1
    3. Base property: exp2(1) = 2
    4. Negative powers: exp2(-1) = 0.5
    5. Positivity: exp2(x) > 0 for all finite x
    6. Monotonicity: if x[i] < x[j], then exp2(x)[i] < exp2(x)[j]
    7. Exponential addition rule: exp2(a + b) = exp2(a) * exp2(b)
    8. Preservation of vector length: result.size = x.size
    9. Handles IEEE 754 floating-point arithmetic

    Precondition: True (no special preconditions for exp2)
    Postcondition: For all indices i, result[i] = 2^x[i] and result[i] > 0
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def exp2 {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem exp2_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    exp2 x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (2 : Float) ^ (x.get i) ∧ 
                               result.get i > 0⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
