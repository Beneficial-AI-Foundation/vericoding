/- 
{
  "name": "numpy.min",
  "category": "Order statistics",
  "description": "Alias for numpy.amin - Return the minimum of an array or minimum along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.min.html",
  "doc": "numpy.min is an alias for numpy.amin. See numpy.amin for full documentation.",
}
-/

/-  numpy.min: Return the minimum of an array or minimum along an axis.

    This function is an alias for numpy.amin that returns the minimum value 
    among all elements in the array. Requires a non-empty array since there 
    is no minimum of an empty set.

    This is a reduction operation that finds the smallest value in the array.
    NaN values are propagated - if any element is NaN, the result will be NaN.
    
    Being an alias, it has identical behavior to amin but provides a more
    intuitive name for the operation.
-/

/-  Specification: min returns the minimum element in the vector.

    Precondition: True (non-empty constraint is enforced by type Vector Float (n + 1))
    Postcondition: result is the minimum value and is an element of the vector
    
    Properties:
    1. The result is actually an element of the input vector
    2. The result is less than or equal to all elements in the vector
    3. This captures the mathematical definition of minimum
    4. As an alias for amin, it has identical mathematical properties
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def min {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem min_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    min a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
