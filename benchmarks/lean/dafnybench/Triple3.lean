import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Triple3: Multiply an integer by 3 (variant 3).
    
    Takes an integer x and returns 3 * x.
    This is variant 3 of the triple specification.
    
    Returns the tripled value.
-/
def triple3 (x : Int) : Int := sorry

/-- Specification: triple3 returns three times the input value.
    
    Precondition: True (no special preconditions)
    Postcondition: result = 3 * x
-/
theorem triple3_spec (x : Int) :
    ⦃⌜True⌝⦄
    (pure (triple3 x) : Id _)
    ⦃⇓result => ⌜result = 3 * x⌝⦄ := by
  sorry
