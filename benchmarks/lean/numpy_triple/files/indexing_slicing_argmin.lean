/- 
{
  "name": "numpy.argmin",
  "category": "Index finding",
  "description": "Returns the indices of the minimum values along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.argmin.html",
  "doc": "Returns the indices of the minimum values along an axis.\n\nParameters\n----------\na : array_like\n    Input array.\naxis : int, optional\n    By default, the index is into the flattened array, otherwise along the specified axis.\nout : array, optional\n    If provided, the result will be inserted into this array.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nindex_array : ndarray of ints\n    Array of indices into the array. It has the same shape as \`\`a.shape\`\` with the dimension along \`axis\` removed.\n\nNotes\n-----\nIn case of multiple occurrences of the minimum values, the indices corresponding to the first occurrence are returned.",
}
-/

/-  numpy.argmin: Returns the index of the minimum value in a vector.
    
    Returns the index of the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.
    
    This function returns the position of the smallest element in the array.
    In case of multiple occurrences of the minimum value, the index of the
    first occurrence is returned.
-/

/-  Specification: argmin returns the index of the minimum element.
    
    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the minimum value,
    and it is the first occurrence of this minimum value in the array.
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def argmin {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem argmin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmin a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get i ≤ a.get j) ∧ 
           (∀ k : Fin (n + 1), k < i → a.get k > a.get i)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
