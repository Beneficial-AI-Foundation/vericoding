import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Check if all characters in a string are digits.
    
    Returns true if all characters in the string are decimal digits (0-9).
    
    Specification from Dafny:
    - result = true iff for all indices i in the string, s[i] is a digit
-/
def allDigits (s : String) : Bool :=
  s.all (fun c => c.isDigit)

/-- Specification: allDigits returns true iff all characters are digits.
    
    Precondition: True (no special preconditions)
    Postcondition: result = true ↔ (∀ i : Fin s.length, s[i].isDigit)
-/
theorem allDigits_spec (s : String) :
    ⦃⌜True⌝⦄
    (pure (allDigits s) : Id _)
    ⦃⇓result => ⌜result ↔ (∀ i : Fin s.length, (s.data.get i).isDigit)⌝⦄ := by
  sorry
