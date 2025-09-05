import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Append an element to an array.
    
    Creates a new array by appending element b to array a.
    
    Specification from Dafny:
    - The result is array a concatenated with singleton array [b]
-/
def arrayAppend (a : Array Int) (b : Int) : Id (Array Int) :=
  a.push b

/-- Specification: arrayAppend creates a new array with b appended.
    
    Precondition: True (no special preconditions)
    Postcondition: result = a ++ [b]
-/
theorem arrayAppend_spec (a : Array Int) (b : Int) :
    ⦃⌜True⌝⦄
    arrayAppend a b
    ⦃⇓result => ⌜result = a.push b⌝⦄ := by
  sorry