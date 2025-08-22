import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- computeIsEven: Determine if an integer is even.

    Returns true if and only if the input integer is divisible by 2.
    
    This is a simple predicate that checks the parity of an integer.
-/
def computeIsEven (x : Int) : Id Bool :=
  pure (x % 2 = 0)

/-- Specification: computeIsEven returns true if and only if x is even.

    Precondition: True (works for any integer)
    Postcondition: The result equals (x % 2 = 0)
    
    This directly specifies that the function correctly identifies even numbers.
-/
theorem computeIsEven_spec (x : Int) :
    ⦃⌜True⌝⦄
    computeIsEven x
    ⦃⇓is_even => ⌜is_even = (x % 2 = 0)⌝⦄ := by
  mvcgen [computeIsEven]
  sorry