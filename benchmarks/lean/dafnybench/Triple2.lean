import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Triple2: Multiply an integer by 3 (variant 2).
    
    Takes an integer x and returns 3 * x.
    This is variant 2 of the triple specification.
    
    Returns the tripled value.
-/
def triple2 (x : Int) : Int := sorry

/-- Specification: triple2 returns three times the input value.
    
    Precondition: True (no special preconditions)
    Postcondition: result = 3 * x
-/
theorem triple2_spec (x : Int) :
    ⦃⌜True⌝⦄
    (pure (triple2 x) : Id _)
    ⦃⇓result => ⌜result = 3 * x⌝⦄ := by
  sorry
