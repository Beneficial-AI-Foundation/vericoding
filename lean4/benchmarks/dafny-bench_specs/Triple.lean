import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Triple: Multiply an integer by 3.

    Takes an integer x and returns 3 * x.

    Returns the tripled value.
-/
def triple (x : Int) : Id Int :=
  3 * x

/-- Specification: triple returns three times the input value.

    Precondition: True (no special preconditions)
    Postcondition: result = 3 * x
-/
theorem triple_spec (x : Int) :
    ⦃⌜True⌝⦄
    triple x
    ⦃⇓result => ⌜result = 3 * x⌝⦄ := by
    sorry
