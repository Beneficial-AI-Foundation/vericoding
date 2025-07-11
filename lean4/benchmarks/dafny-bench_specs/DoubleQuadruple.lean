import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- DoubleQuadruple: Calculate double and quadruple of an integer.

    Returns a pair (a, b) where a is twice the input and b is four times the input.
-/
def doubleQuadruple (x : Int) : Id (Int × Int) :=
  sorry

/-- Specification: DoubleQuadruple returns 2x and 4x.

    Precondition: True (works for any integer)
    Postcondition: a = 2 * x and b = 4 * x
-/
theorem doubleQuadruple_spec (x : Int) :
    ⦃⌜True⌝⦄
    doubleQuadruple x
    ⦃⇓result => ⌜result.1 = 2 * x ∧ result.2 = 4 * x⌝⦄ := by
  sorry