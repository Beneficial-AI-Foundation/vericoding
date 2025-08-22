import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.left_shift",
  "category": "Bit shifting",
  "description": "Shift the bits of an integer to the left",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.left_shift.html",
  "doc": "Shift the bits of an integer to the left.\n\nBits are shifted to the left by appending x2 0s at the right of x1. Since the internal representation of numbers is in binary format, this operation is equivalent to multiplying x1 by 2**x2.\n\nParameters\n----------\nx1 : array_like of integer type\n    Input values.\nx2 : array_like of integer type\n    Number of zeros to append to x1. Has to be non-negative.\n    If x1.shape != x2.shape, they must be broadcastable to a common shape.\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored.\nwhere : array_like, optional\n    This condition is broadcast over the input.\n\nReturns\n-------\nout : ndarray of integer type\n    Return x1 with bits shifted x2 times to the left.\n    This is a scalar if both x1 and x2 are scalars.\n\nSee Also\n--------\nright_shift : Shift the bits of an integer to the right.\nbinary_repr : Return the binary representation of the input number as a string.\n\nExamples\n--------\n>>> np.left_shift(5, 2)\n20\n>>> np.left_shift(5, [1,2,3])\narray([10, 20, 40])\n\nNote that the dtype of the second argument may change the dtype of the result and can lead to unexpected results in some cases:\n\n>>> a = np.left_shift(np.uint8(255), 1) # Expect 254\n>>> print(a, type(a)) # Unexpected result due to upcasting\n510 <class 'numpy.int64'>\n>>> b = np.left_shift(np.uint8(255), np.uint8(1))\n>>> print(b, type(b))\n254 <class 'numpy.uint8'>",
  "code": "# C implementation for performance\n# Shift the bits of an integer to the left\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/core/src/umath/loops.c.src:\n\n/**begin repeat\n * #kind = left_shift, right_shift#\n * #OP = <<, >>#\n */\n\nBINARY_LOOP_FAST(INT, @INT@, *out = npy_lshift@c@(in1, in2))\n\n/* The implementation uses safe shift functions that handle\n * platform-specific behavior and prevent undefined behavior\n * from shifting by more bits than the type width */\n\n/* npy_lshift functions ensure the behavior is independent of\n * whether a compiler's shift instructions mask the count by\n * the number of bits in the type, which can produce\n * surprising results. */"
}
-/

open Std.Do

/-- Shift the bits of integers to the left element-wise.
    This operation is equivalent to multiplying each element by 2^shift_amount. -/
def left_shift {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: left_shift performs bitwise left shift operation on each element.
    The result is equivalent to multiplying x1[i] by 2^x2[i] for non-negative shifts.
    
    Mathematical properties:
    1. Core behavior: Each element result[i] = x1[i] * 2^x2[i] for non-negative shifts
    2. Identity property: Shifting by 0 returns the original value
    3. Zero preservation: Shifting zero always yields zero
    4. Monotonicity: For positive values, left shifting increases magnitude
    5. Composition property: left_shift(x, a) then left_shift(result, b) = left_shift(x, a+b) -/
theorem left_shift_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_nonneg : ∀ i : Fin n, x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x2.get i ≥ 0⌝⦄
    left_shift x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = x1.get i * (2 ^ (x2.get i).toNat)) ∧
                 (∀ i : Fin n, x2.get i = 0 → result.get i = x1.get i) ∧
                 (∀ i : Fin n, x1.get i = 0 → result.get i = 0) ∧
                 (∀ i : Fin n, x1.get i > 0 ∧ x2.get i > 0 → result.get i > x1.get i) ∧
                 (∀ i : Fin n, x1.get i < 0 ∧ x2.get i > 0 → result.get i < x1.get i)⌝⦄ := by
  sorry