import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Reverse: Reverse an array in-place.

    Modifies the input array so that elements appear in reverse order.
    The first element becomes the last, the second becomes second-to-last, etc.

    The array is modified in-place.
-/
def reverse (a : Array Int) : Id (Array Int) :=
  Array.ofFn fun i : Fin a.size => a[a.size - 1 - i.val]'(by sorry)

/-- Specification: reverse modifies the array so that each element
    at position i is moved to position (length - 1 - i).

    Precondition: True (no special preconditions)
    Postcondition: Each element is at its reversed position
-/
theorem reverse_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    reverse a
    ⦃⇓result => ⌜result.size = a.size ∧
                 ∀ i : Fin a.size, result[i.val]'(by sorry) = a[a.size - 1 - i.val]'(by sorry)⌝⦄ := by
  sorry