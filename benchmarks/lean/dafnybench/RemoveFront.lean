import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- RemoveFront: Remove the first element from an array.

    Creates a new array containing all elements except the first one.
    The input array must have at least one element.

    Returns a new array with length one less than the input.
-/
def removeFront {α : Type} (a : Array α) : Id (Array α) :=
  if h : a.size > 0 then
    Array.ofFn fun i : Fin (a.size - 1) => a[i.val + 1]'(by sorry)
  else
    panic! "Array must have at least one element"

/-- Specification: removeFront returns an array containing all elements
    except the first one from the input array.

    Precondition: The input array must have at least one element
    Postcondition: The result contains exactly the elements from index 1 onwards
-/
theorem removeFront_spec {α : Type} (a : Array α) (h : a.size > 0) :
    ⦃⌜a.size > 0⌝⦄
    removeFront a
    ⦃⇓result => ⌜result.size = a.size - 1 ∧ 
                 ∀ i : Fin result.size, result[i] = a[i.val + 1]'(by sorry)⌝⦄ := by
  sorry