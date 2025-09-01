/- 
{
  "name": "numpy.invert",
  "category": "Elementwise bit operations",
  "description": "Compute bit-wise inversion, or bit-wise NOT, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.invert.html",
  "doc": "Compute bit-wise inversion, or bit-wise NOT, element-wise.\n\nComputes the bit-wise NOT of the underlying binary representation of the integers in the input arrays. This ufunc implements the C/Python operator ~.\n\nFor signed integer inputs, the two's complement is returned. In a two's-complement system negative numbers are represented by the two's complement of the absolute value. This is the most common method of representing signed integers on computers. A N-bit two's-complement system can represent every integer in the range -2^(N-1) to +2^(N-1)-1.\n\nParameters\n----------\nx : array_like\n    Only integer and boolean types are handled.\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored.\nwhere : array_like, optional\n    This condition is broadcast over the input.\n\nReturns\n-------\nout : ndarray or scalar\n    Result.\n\nNotes\n-----\nbitwise_not is an alias for invert:\n\n>>> np.bitwise_not is np.invert\nTrue\n\nExamples\n--------\n>>> np.invert(np.array([13], dtype=np.uint8))\narray([242], dtype=uint8)\n>>> np.invert(np.array([13], dtype=np.uint16))\narray([65522], dtype=uint16)\n>>> np.invert(np.array([13], dtype=np.int8))\narray([-14], dtype=int8)\n>>> np.invert(np.array([True, False]))\narray([False, True])",
}
-/

/-  Compute bit-wise inversion (NOT) of each element in a vector of integers.
    For signed integers, this returns the two's complement. -/

/-  Specification: invert computes the bitwise NOT operation element-wise.
    
    Mathematical properties:
    1. Two's complement relationship: ~x = -(x + 1)
    2. Involution property: applying invert twice returns the original value
    3. The operation preserves vector size
    4. Identity relationships:
       - ~0 = -1
       - ~(-1) = 0
    5. Sign flipping: ~x has opposite sign to x when x ≠ -1
    
    The specification captures both the element-wise nature and the 
    mathematical relationship for two's complement representation. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def invert {n : Nat} (x : Vector Int n) : Id (Vector Int n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem invert_spec {n : Nat} (x : Vector Int n) :
    ⦃⌜True⌝⦄
    invert x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = -(x.get i + 1)) ∧
                 (result.size = n) ∧
                 (∀ i : Fin n, x.get i = 0 → result.get i = -1) ∧
                 (∀ i : Fin n, x.get i = -1 → result.get i = 0) ∧
                 (∀ i : Fin n, x.get i ≠ -1 → (x.get i > 0 ↔ result.get i < 0))⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
