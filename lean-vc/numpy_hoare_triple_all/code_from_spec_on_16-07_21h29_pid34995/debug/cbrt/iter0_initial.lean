import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.cbrt",
  "description": "Return the cube-root of an array, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.cbrt.html",
  "doc": "Return the cube-root of an array, element-wise.",
  "code": "# Universal function (ufunc) implemented in C\n# This is a wrapper around the C math library's cbrt function\n# The ufunc infrastructure handles:\n# - Broadcasting across arrays\n# - Type casting and promotion\n# - Output array allocation\n# - Vectorization for performance\n#\n# Conceptual Python equivalent:\ndef cbrt(x, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True):\n    '''Return the cube-root of an array, element-wise'''\n    # Handle array conversion and broadcasting\n    x = np.asanyarray(x)\n    \n    # Apply cbrt function element-wise\n    # In practice, this calls the C math library's cbrt()\n    # with optimized loops for different data types\n    return _apply_ufunc(math.cbrt, x, out=out, where=where,\n                       casting=casting, order=order, dtype=dtype, subok=subok)"
}
-/

open Std.Do

-- LLM HELPER
def float_cbrt (x : Float) : Float :=
  if x >= 0 then
    x ^ (1.0 / 3.0)
  else
    -((-x) ^ (1.0 / 3.0))

-- LLM HELPER
lemma float_cbrt_cube (x : Float) : (float_cbrt x) ^ 3 = x := by
  simp [float_cbrt]
  split_ifs with h
  · simp [Float.pow_def]
    ring_nf
  · simp [Float.pow_def]
    ring_nf

/-- numpy.cbrt: Return the cube-root of an array, element-wise.

    Computes the cube root of each element in the input array.
    The cube root function is defined for all real numbers, including negative numbers.
    For any real number x, cbrt(x) = y such that y³ = x.

    Returns an array of the same shape as x, containing the cube roots.
-/
def cbrt {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map float_cbrt)

/-- Specification: numpy.cbrt returns a vector where each element is the
    cube root of the corresponding element in x.

    Precondition: True (cube root is defined for all real numbers)
    Postcondition: For all indices i, (result[i])³ = x[i]
    
    Mathematical properties:
    - cbrt(x³) = x for all x
    - cbrt(-x) = -cbrt(x) (odd function)
    - cbrt(0) = 0
    - cbrt(1) = 1
    - cbrt(8) = 2
    - cbrt(-8) = -2
-/
theorem cbrt_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    cbrt x
    ⦃⇓result => ⌜∀ i : Fin n, (result.get i) ^ 3 = x.get i⌝⦄ := by
  simp [cbrt]
  intro i
  rw [Vector.get_map]
  exact float_cbrt_cube (x.get i)