import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.bitwise_count",
  "category": "Bit counting",
  "description": "Computes the number of 1-bits in the absolute value of x",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.bitwise_count.html",
  "doc": "Computes the number of 1-bits in the absolute value of x.\n\nAnalogous to the builtin int.bit_count or popcount in C++.\n\nParameters\n----------\nx : array_like, unsigned int\n    Input array.\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored. If provided, it must have a shape that the inputs broadcast to. If not provided or None, a freshly-allocated array is returned.\nwhere : array_like, optional\n    This condition is broadcast over the input. At locations where the condition is True, the out array will be set to the ufunc result.\n\nReturns\n-------\ny : ndarray\n    The corresponding number of 1-bits in the input.\n    Returns uint8 for all integer types.\n    This is a scalar if x is a scalar.\n\nReferences\n----------\n.. [1] Wikipedia, \"Hamming weight\",\n       https://en.wikipedia.org/wiki/Hamming_weight\n.. [2] http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel\n.. [3] https://aggregate.ee.engr.uky.edu/MAGIC/#Population%20Count%20(Ones%20Count)\n\nExamples\n--------\n>>> np.bitwise_count(1023)\nnp.uint8(10)\n>>> a = np.array([2**i - 1 for i in range(16)])\n>>> np.bitwise_count(a)\narray([ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],\n      dtype=uint8)",
  "code": "# C implementation for performance\n# Computes the number of 1-bits in the absolute value of x\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in numpy/core/src/umath/loops.c.src and npy_math.h:\n\n/* Popcount implementation from PR #19355 */\n/* Uses CountBitsSetParallel algorithm which takes 12 operations */\n\nstatic NPY_INLINE int\nnpy_popcount_parallel(npy_uintp a) {\n    /* CountBitsSetParallel algorithm */\n    a = a - ((a >> 1) & 0x5555555555555555ULL);\n    a = (a & 0x3333333333333333ULL) + ((a >> 2) & 0x3333333333333333ULL);\n    return (((a + (a >> 4)) & 0xF0F0F0F0F0F0F0FULL) * 0x101010101010101ULL) >> 56;\n}\n\n/* Platform-specific optimizations */\n#if defined(__GNUC__) || defined(__clang__)\n    /* Use builtin popcount when available */\n    #define npy_popcount(x) __builtin_popcountll(x)\n#elif defined(_MSC_VER)\n    /* Use Windows intrinsic */\n    #include <intrin.h>\n    #define npy_popcount(x) __popcnt64(x)\n#else\n    /* Fallback to parallel algorithm */\n    #define npy_popcount(x) npy_popcount_parallel(x)\n#endif\n\n/* Ufunc loop */\nUNARY_LOOP_FAST(ULONG, npy_uint8, *out = npy_popcount(in))"
}
-/

open Std.Do

/-- Helper function to count the number of 1-bits in a natural number -/
def popcount (n : Nat) : Nat :=
  if n = 0 then 0 else (n % 2) + popcount (n / 2)

/-- Computes the number of 1-bits in the absolute value of each element in a vector -/
def bitwise_count {n : Nat} (x : Vector Int n) : Id (Vector Nat n) :=
  sorry

/-- Specification: bitwise_count returns the count of 1-bits in the binary representation
    of the absolute value of each element. The result satisfies several properties:
    1. Each output element is the popcount of the corresponding input's absolute value
    2. The popcount is bounded by the number of bits in the representation
    3. Zero inputs produce zero outputs
    4. Powers of 2 have exactly one bit set
    5. Powers of 2 minus 1 have consecutive 1-bits (e.g., 2^k - 1 has k bits set)
    6. The popcount is always non-negative and bounded by bit width
    7. For negative inputs, uses the absolute value
    8. The popcount operation is invariant under sign changes -/
theorem bitwise_count_spec {n : Nat} (x : Vector Int n) :
    ⦃⌜True⌝⦄
    bitwise_count x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = popcount (Int.natAbs (x.get i))) ∧
                 (∀ i : Fin n, result.get i ≤ (Int.natAbs (x.get i)).log2 + 1) ∧
                 (∀ i : Fin n, x.get i = 0 → result.get i = 0) ∧
                 (∀ i : Fin n, ∀ k : Nat, k > 0 → x.get i = 2^k → result.get i = 1) ∧
                 (∀ i : Fin n, ∀ k : Nat, k > 0 → x.get i = 2^k - 1 → result.get i = k) ∧
                 (∀ i : Fin n, result.get i ≥ 0) ∧
                 (∀ i : Fin n, x.get i < 0 → result.get i = popcount (Int.natAbs (x.get i))) ∧
                 (∀ i : Fin n, ∀ m : Int, x.get i = m → result.get i = popcount (Int.natAbs m)) ∧
                 (∀ i : Fin n, ∀ j : Fin n, x.get i = -(x.get j) → result.get i = result.get j)⌝⦄ := by
  sorry