import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- SeqToArray: Convert a list (sequence) to an array.

    Creates a fresh array containing all elements from the input list
    in the same order.

    Returns a new array with the same elements as the list.
-/
def seqToArray {α : Type} (xs : List α) : Id (Array α) :=
  xs.toArray

/-- Specification: seqToArray creates an array with the same length
    and elements as the input list.

    Precondition: True (no special preconditions)
    Postcondition: Array has same length and elements as list
-/
theorem seqToArray_spec {α : Type} (xs : List α) :
    ⦃⌜True⌝⦄
    seqToArray xs
    ⦃⇓result => ⌜result.size = xs.length ∧
                 ∀ i : Fin xs.length, result[i.val]'(by sorry) = xs[i]⌝⦄ := by
  sorry