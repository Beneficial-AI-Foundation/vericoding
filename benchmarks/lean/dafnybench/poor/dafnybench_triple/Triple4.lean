import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Triple4: Multiply an integer by 3 (variant 4).
    
    Takes an integer x and returns 3 * x.
    This is variant 4 of the triple specification.
    
    Returns the tripled value.
-/
def triple4 (x : Int) : Id Int :=
  3 * x

/-- Specification: triple4 returns three times the input value.
    
    Precondition: True (no special preconditions)
    Postcondition: result = 3 * x
-/
theorem triple4_spec (x : Int) :
    ⦃⌜True⌝⦄
    triple4 x
    ⦃⇓result => ⌜result = 3 * x⌝⦄ := by
  sorry