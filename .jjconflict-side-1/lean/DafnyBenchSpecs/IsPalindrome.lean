import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- isPalindrome: Check if a sequence of characters is a palindrome.

    A palindrome reads the same forwards and backwards. This function
    checks if a given sequence of characters has this property.
    
    Examples:
    - "racecar" is a palindrome
    - "hello" is not a palindrome
    - "" (empty string) is a palindrome
-/
def isPalindrome (x : List Char) : Id Bool :=
  pure (x = x.reverse)

/-- Specification: isPalindrome returns true if and only if the sequence reads
    the same forwards and backwards.

    Precondition: True (works for any character sequence)
    Postcondition: The result is true iff for all valid indices i, x[i] = x[|x| - i - 1]
    
    This specifies that characters at symmetric positions must be equal.
-/
theorem isPalindrome_spec (x : List Char) :
    ⦃⌜True⌝⦄
    isPalindrome x
    ⦃⇓result => ⌜result = true ↔ (∀ i : Fin x.length, x[i] = x[x.length - i.val - 1])⌝⦄ := by
  mvcgen [isPalindrome]
  sorry