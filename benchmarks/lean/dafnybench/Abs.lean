import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Absolute value function.
    
    Computes the absolute value of an integer x.
    
    Specification from Dafny:
    - If x >= 0, then result = x
    - If x < 0, then x + result = 0 (i.e., result = -x)
-/
def abs (x : Int) : Int :=
  if x >= 0 then x else -x

/-- Specification: abs returns the absolute value of x.
    
    Precondition: True (no special preconditions)
    Postcondition: 
    - If x >= 0, then result = x
    - If x < 0, then x + result = 0
-/
theorem abs_spec (x : Int) :
    ⦃⌜True⌝⦄
    (pure (abs x) : Id _)
    ⦃⇓result => ⌜(x >= 0 → result = x) ∧ (x < 0 → x + result = 0)⌝⦄ := by
  sorry
