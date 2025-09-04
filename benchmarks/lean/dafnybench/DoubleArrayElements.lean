import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- DoubleArrayElements: Double each element in an array in-place.

    Modifies the input array by multiplying each element by 2.
-/
def doubleArrayElements (s : Array Int) : Id (Array Int) :=
  sorry

/-- Specification: DoubleArrayElements doubles all elements.

    Precondition: True (no special preconditions)
    Postcondition: Each element in the result is twice the corresponding original element
-/
theorem doubleArrayElements_spec (s : Array Int) :
    ⦃⌜True⌝⦄
    doubleArrayElements s
    ⦃⇓result => ⌜result.size = s.size ∧ 
                  ∀ i : Fin s.size, result[i.val]? = some (2 * s[i])⌝⦄ := by
  sorry