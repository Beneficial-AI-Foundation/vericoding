import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Copy an array.
    
    Creates a new array that is an exact copy of the input array.
    
    Specification from Dafny:
    - result.length = source.length
    - For all valid indices i, result[i] = source[i]
-/
def arrayCopy {α : Type} (s : Array α) : Array α :=
  s.toList.toArray

/-- Specification: arrayCopy creates an identical copy.
    
    Precondition: True (no special preconditions)
    Postcondition: 
    - result.size = s.size
    - For all i < s.size, result[i] = s[i]
-/
theorem arrayCopy_spec {α : Type} (s : Array α) :
    ⦃⌜True⌝⦄
    (pure (arrayCopy s) : Id _)
    ⦃⇓result => ⌜result.size = s.size ∧ 
                 (∀ i : Fin s.size, result[i.val]'(by sorry) = s[i])⌝⦄ := by
  sorry
