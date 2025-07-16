import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Quotient: Integer division with remainder.
    
    Given two natural numbers x and y (with y ≠ 0), computes the quotient q
    and remainder r such that x = q * y + r and 0 ≤ r < y.
    
    Example: Quotient(17, 5) = (r=2, q=3) because 17 = 3 * 5 + 2
-/
def quotient (x y : Nat) : Id (Int × Int) :=
  (x % y, x / y)

/-- Specification: quotient computes integer division with remainder correctly.
    
    Precondition: y ≠ 0
    Postcondition: 
    - q * y + r = x
    - 0 ≤ r < y
    - 0 ≤ q
-/
theorem quotient_spec (x y : Nat) :
    ⦃⌜y ≠ 0⌝⦄
    quotient x y
    ⦃⇓(r, q) => ⌜
      q * y + r = x ∧ 
      0 ≤ r ∧ r < y ∧ 
      0 ≤ q
    ⌝⦄ := by
  sorry