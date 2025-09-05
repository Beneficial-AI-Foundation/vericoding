import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Match: Check if a string matches a pattern with '?' wildcards.
    
    Given two strings of equal length, checks if they match where '?' in the pattern
    can match any character in the string.
    
    Example: Match("hello", "h?llo") = true
-/
def matchPattern (s p : String) : Bool := sorry

/-- Specification: match returns true if and only if for all positions,
    either the characters match or the pattern has a '?' at that position.
    
    Precondition: The strings have equal length
    Postcondition: Result is true iff for all indices, s[i] = p[i] or p[i] = '?'
-/
theorem matchPattern_spec (s p : String) :
    ⦃⌜s.length = p.length⌝⦄
    (pure (matchPattern s p) : Id _)
    ⦃⇓result => ⌜result ↔ ∀ n : Nat, n < s.length → 
      (s.data.get? n = p.data.get? n ∨ p.data.get? n = some '?')⌝⦄ := by
  sorry
