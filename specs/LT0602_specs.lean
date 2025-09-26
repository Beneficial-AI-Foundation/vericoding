-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.add",
  "category": "String operations",
  "description": "Add arguments element-wise (string concatenation)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.add.html",
  "doc": "Add arguments element-wise.\n\nFor string arrays, this concatenates the strings element-wise.\n\nParameters\n----------\nx1, x2 : array_like\n    Input arrays to be added element-wise.\n    Must be broadcastable to a common shape.\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored.\nwhere : array_like, optional\n    This condition is broadcast over the input.\nkwargs\n    For other keyword-only arguments, see the ufunc docs.\n\nReturns\n-------\nadd : ndarray or scalar\n    The concatenated strings, element-wise.\n\nExamples\n--------\n>>> np.strings.add([\"num\", \"doc\"], [\"py\", \"umentation\"])\narray(['numpy', 'documentation'], dtype='<U13')",
  "code": "# Universal function (ufunc) implemented in C\n# Add arguments element-wise (string concatenation)\n# \n# This function is implemented as a compiled ufunc in NumPy's C extension modules.\n# The ufunc infrastructure provides:\n# - Element-wise operations with broadcasting\n# - Type casting and promotion rules\n# - Output array allocation and memory management\n# - Optimized loops for different data types\n# - Support for where parameter (conditional operation)\n# - Vectorized execution using SIMD instructions where available\n#\n# For more details, see numpy/_core/src/umath/"
}
-/

/-- numpy.strings.add: Add arguments element-wise (string concatenation).

    Concatenates two vectors of strings element-wise. Each element of the result
    is the concatenation of the corresponding elements from the input vectors.

    This is equivalent to string concatenation using the + operator for each
    element pair. The function preserves the shape of the input arrays and
    handles empty strings appropriately.

    From NumPy documentation:
    - Parameters: x1, x2 (array_like) - Input arrays with string dtype
    - Returns: add (ndarray) - The concatenated strings, element-wise

    Mathematical Properties:
    1. Element-wise concatenation: result[i] = x1[i] ++ x2[i]
    2. Associativity: add(add(x1, x2), x3) = add(x1, add(x2, x3))
    3. Identity with empty strings: add(x, empty_vector) = x
    4. Preserves vector length: result.size = x1.size = x2.size
    5. Non-commutative: add(x1, x2) ≠ add(x2, x1) in general
-/
def add {n : Nat} (x1 x2 : Vector String n) : Id (Vector String n) :=
  Vector.zipWith (· ++ ·) x1 x2

/-- Specification: numpy.strings.add returns a vector where each element is the
    concatenation of the corresponding elements from x1 and x2.

    Mathematical Properties:
    1. Element-wise correctness: result[i] = x1[i] ++ x2[i] for all i
    2. Associativity: For any three string vectors a, b, c of the same length,
       add(add(a, b), c) = add(a, add(b, c))
    3. Identity with empty strings: add(x, zeros) = x where zeros is a vector of empty strings
    4. Preserves vector length: result.size = x1.size = x2.size
    5. String concatenation properties: preserves individual string properties

    Precondition: True (no special preconditions for string concatenation)
    Postcondition: For all indices i, result[i] = x1[i] ++ x2[i]
-/
theorem add_spec {n : Nat} (x1 x2 : Vector String n) :
    ⦃⌜True⌝⦄
    add x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i ++ x2.get i⌝⦄ := by
  sorry

-- Additional properties for comprehensive specification
theorem add_associativity {n : Nat} (x1 x2 x3 : Vector String n) :
    add (add x1 x2) x3 = add x1 (add x2 x3) := by
  sorry

theorem add_identity_left {n : Nat} (x : Vector String n) :
    add (Vector.replicate n "") x = x := by
  sorry

theorem add_identity_right {n : Nat} (x : Vector String n) :
    add x (Vector.replicate n "") = x := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>