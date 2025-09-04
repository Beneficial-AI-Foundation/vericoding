import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Rotate: Rotate an array by a given offset.

    Creates a new array where each element is shifted by the given offset.
    Elements that would go past the end wrap around to the beginning.

    Returns a new array of the same length with rotated elements.
-/
def rotate (a : Array Int) (offset : Nat) : Id (Array Int) :=
  if a.size = 0 then 
    a
  else
    Array.ofFn fun i : Fin a.size => a[(i.val + offset) % a.size]'(by sorry)

/-- Specification: rotate returns a new array where each element
    at position i comes from position (i + offset) % length.

    Precondition: offset must be non-negative
    Postcondition: Elements are cyclically shifted by offset positions
-/
theorem rotate_spec (a : Array Int) (offset : Nat) :
    ⦃⌜offset ≥ 0⌝⦄
    rotate a offset
    ⦃⇓result => ⌜result.size = a.size ∧
                 ∀ i : Fin a.size, result[i.val]'(by sorry) = a[(i.val + offset) % a.size]'(by sorry)⌝⦄ := by
  sorry