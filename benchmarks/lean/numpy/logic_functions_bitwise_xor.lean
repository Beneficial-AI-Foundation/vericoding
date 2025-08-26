import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.bitwise_xor",
  "category": "Logical operations",
  "description": "Compute the bit-wise XOR of two arrays element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.bitwise_xor.html",
  "doc": "Compute the bit-wise XOR of two arrays element-wise.\n\nComputes the bit-wise XOR of the underlying binary representation of\nthe integers in the input arrays. This ufunc implements the C/Python\noperator ^.\n\nParameters\n----------\nx1, x2 : array_like\n    Only integer and boolean types are handled.\n    If x1.shape != x2.shape, they must be broadcastable to a common\n    shape (which becomes the shape of the output).\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored. If provided, it must have\n    a shape that the inputs broadcast to. If not provided or None,\n    a freshly-allocated array is returned. A tuple (possible only as a\n    keyword argument) must have length equal to the number of outputs.\nwhere : array_like, optional\n    This condition is broadcast over the input. At locations where the\n    condition is True, the out array will be set to the ufunc result.\n    Elsewhere, the out array will retain its original value.\n    Note that if an uninitialized out array is created via the default\n    out=None, locations within it where the condition is False will\n    remain uninitialized.\n**kwargs\n    For other keyword-only arguments, see the\n    ufunc docs.\n\nReturns\n-------\nout : ndarray or scalar\n    Result.\n    This is a scalar if both x1 and x2 are scalars.\n\nSee Also\n--------\nlogical_xor\nbitwise_and, bitwise_or\nbinary_repr :\n    Return the binary representation of the input number as a string.\n\nExamples\n--------\nThe number 13 is represented by 00001101. Likewise, 17 is\nrepresented by 00010001.  The bit-wise XOR of 13 and 17 is\ntherefore 00011100, or 28:\n\n>>> np.bitwise_xor(13, 17)\n28\n>>> np.binary_repr(28)\n'11100'\n\n>>> np.bitwise_xor(31, 5)\n26\n>>> np.bitwise_xor([31,3], 5)\narray([26,  6])\n\n>>> np.bitwise_xor([31,3], [5,6])\narray([26,  5])\n>>> np.bitwise_xor([True, True], [False, True])\narray([ True, False])\n\nThe ^ operator can be used as a shorthand for np.bitwise_xor on\nndarrays.\n\n>>> x1 = np.array([True, True])\n>>> x2 = np.array([False, True])\n>>> x1 ^ x2\narray([ True, False])",
  "code": "C implementation: ufunc 'bitwise_xor'"
}
-/

open Std.Do

/-- numpy.bitwise_xor: Compute the bit-wise XOR of two arrays element-wise.

    Computes the bit-wise XOR of the underlying binary representation of
    the integers in the input arrays. This ufunc implements the C/Python
    operator ^.

    The function works on integer and boolean types, computing the XOR
    of corresponding elements from two input vectors.
-/
def bitwise_xor {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: numpy.bitwise_xor returns a vector where each element is the 
    bitwise XOR of the corresponding elements from x1 and x2.

    Precondition: All elements are non-negative (to use well-defined bitwise operations)
    Postcondition: For all indices i, result[i] = x1[i] XOR x2[i]
    
    Mathematical properties:
    - XOR is commutative: x1[i] XOR x2[i] = x2[i] XOR x1[i]
    - XOR is associative: (a XOR b) XOR c = a XOR (b XOR c)
    - XOR with zero is identity: x XOR 0 = x
    - XOR is self-inverse: x XOR x = 0
-/
theorem bitwise_xor_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_nonneg : ∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0⌝⦄
    bitwise_xor x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = Int.ofNat (Int.toNat (x1.get i) ^^^ Int.toNat (x2.get i))) ∧
                (∀ i : Fin n, result.get i ≥ 0) ∧
                (∀ i : Fin n, x1.get i = 0 → result.get i = x2.get i) ∧
                (∀ i : Fin n, x2.get i = 0 → result.get i = x1.get i) ∧
                (∀ i : Fin n, x1.get i = x2.get i → result.get i = 0)⌝⦄ := by
  sorry