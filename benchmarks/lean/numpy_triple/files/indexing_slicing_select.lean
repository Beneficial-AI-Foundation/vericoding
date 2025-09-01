/- 
{
  "name": "numpy.select",
  "category": "Basic indexing",
  "description": "Return an array drawn from elements in choicelist, depending on conditions",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.select.html",
  "doc": "Return an array drawn from elements in choicelist, depending on conditions.\n\nParameters\n----------\ncondlist : list of bool ndarrays\n    The list of conditions which determine from which array in \`choicelist\`\n    the output elements are taken. When multiple conditions are satisfied,\n    the first one encountered in \`condlist\` is used.\nchoicelist : list of ndarrays\n    The list of arrays from which the output elements are taken. It has\n    to be of the same length as \`condlist\`.\ndefault : scalar, optional\n    The element inserted in \`output\` when all conditions evaluate to False.\n\nReturns\n-------\noutput : ndarray\n    The output at position m is the m-th element of the array in\n    \`choicelist\` where the m-th element of the corresponding array in\n    \`condlist\` is True.",
}
-/

/-  numpy.select: Return an array drawn from elements in choicelist, depending on conditions.
    
    For each element position, returns the element from the first choice array
    where the corresponding condition is True. If no conditions are True,
    returns the default value.
    
    This function enables multi-way conditional selection between arrays.
-/

/-  Specification: numpy.select performs element-wise multi-conditional selection.
    
    Precondition: condlist and choicelist have the same length
    Postcondition: Each element is selected from the first matching choice array,
                   or default if no conditions match
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def select {n : Nat} {k : Nat} (condlist : Vector (Vector Bool n) k) (choicelist : Vector (Vector Float n) k) (default : Float) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem select_spec {n : Nat} {k : Nat} (condlist : Vector (Vector Bool n) k) (choicelist : Vector (Vector Float n) k) (default : Float) :
    ⦃⌜True⌝⦄
    select condlist choicelist default
    ⦃⇓result => ⌜∀ i : Fin n, 
      (∃ j : Fin k, (condlist.get j).get i = true ∧ 
        result.get i = (choicelist.get j).get i ∧
        (∀ j' : Fin k, j' < j → (condlist.get j').get i = false)) ∨
      (∀ j : Fin k, (condlist.get j).get i = false ∧ result.get i = default)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
