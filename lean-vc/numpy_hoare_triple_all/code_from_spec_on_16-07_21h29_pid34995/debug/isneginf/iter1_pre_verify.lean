import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.isneginf",
  "category": "Array contents testing",
  "description": "Test element-wise for negative infinity, return result as bool array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.isneginf.html",
  "doc": "Test element-wise for negative infinity, return result as bool array.\n\nParameters\n----------\nx : array_like\n    The input array.\nout : array_like, optional\n    A location into which the result is stored. If provided, it must have a\n    shape that the input broadcasts to. If not provided or None, a\n    freshly-allocated boolean array is returned.\n\nReturns\n-------\nout : ndarray\n    A boolean array with the same dimensions as the input.\n    If second argument is not supplied then a numpy boolean array is\n    returned with values True where the corresponding element of the\n    input is negative infinity and values False where the element of\n    the input is not negative infinity.\n    \n    If a second argument is supplied the result is stored there. If the\n    type of that array is a numeric type the result is represented as\n    zeros and ones, if the type is boolean then as False and True. The\n    return value out is then a reference to that array.\n\nSee Also\n--------\nisinf, isposinf, isnan, isfinite\n\nNotes\n-----\nNumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic\n(IEEE 754).\n\nErrors result if the second argument is also supplied when x is a\nscalar input, if first and second arguments have different shapes,\nor if the first argument has complex values.\n\nExamples\n--------\n>>> np.isneginf(np.NINF)\nTrue\n>>> np.isneginf(np.inf)\nFalse\n>>> np.isneginf(np.PINF)\nFalse\n>>> np.isneginf([-np.inf, 0., np.inf])\narray([ True, False, False])\n\n>>> x = np.array([-np.inf, 0., np.inf])\n>>> y = np.array([2, 2, 2])\n>>> np.isneginf(x, y)\narray([1, 0, 0])\n>>> y\narray([1, 0, 0])",
  "code": "def isneginf(x, out=None):\n    \"\"\"\n    Test element-wise for negative infinity, return result as bool array.\n    \n    Parameters\n    ----------\n    x : array_like\n        The input array.\n    out : array_like, optional\n        A location into which the result is stored. If provided, it must have a\n        shape that the input broadcasts to. If not provided or None, a\n        freshly-allocated boolean array is returned.\n    \n    Returns\n    -------\n    out : ndarray\n        A boolean array with the same dimensions as the input.\n        If second argument is not supplied then a numpy boolean array is\n        returned with values True where the corresponding element of the\n        input is negative infinity and values False where the element of\n        the input is not negative infinity.\n        \n        If a second argument is supplied the result is stored there. If the\n        type of that array is a numeric type the result is represented as\n        zeros and ones, if the type is boolean then as False and True. The\n        return value \`out\` is then a reference to that array.\n    \n    See Also\n    --------\n    isinf, isposinf, isnan, isfinite\n    \n    Notes\n    -----\n    NumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic\n    (IEEE 754).\n    \n    Errors result if the second argument is also supplied when x is a\n    scalar input, if first and second arguments have different shapes,\n    or if the first argument has complex values.\n    \n    Examples\n    --------\n    >>> np.isneginf(np.NINF)\n    True\n    >>> np.isneginf(np.inf)\n    False\n    >>> np.isneginf(np.PINF)\n    False\n    >>> np.isneginf([-np.inf, 0., np.inf])\n    array([ True, False, False])\n    \n    >>> x = np.array([-np.inf, 0., np.inf])\n    >>> y = np.array([2, 2, 2])\n    >>> np.isneginf(x, y)\n    array([1, 0, 0])\n    >>> y\n    array([1, 0, 0])\n    \n    \"\"\"\n    is_inf = nx.isinf(x)\n    try:\n        signbit = nx.signbit(x)\n    except TypeError as e:\n        dtype = nx.asanyarray(x).dtype\n        raise TypeError(f'This operation is not supported for {dtype} values '\n                        'because it would be ambiguous.') from e\n    else:\n        return nx.logical_and(is_inf, signbit, out)"
}
-/

-- LLM HELPER
def isNegInf (x : Float) : Bool :=
  x.isInf ∧ x < 0

/-- Test element-wise for negative infinity, return result as bool array. -/
def isneginf {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  Vector.map isNegInf x

/-- Specification: isneginf returns True for negative infinity elements, False otherwise.
    
    This function tests each element according to IEEE 754 floating-point standard:
    - Returns true if the element is negative infinity (-∞)
    - Returns false for all other values including positive infinity, NaN, finite numbers, and zero
    
    Mathematical properties:
    1. Negative infinity detection: result[i] = true iff x[i] is negative infinity
    2. Distinction from positive infinity: only negative infinity returns true
    3. Distinction from NaN: negative infinity and NaN are mutually exclusive
    4. Result preserves shape: output vector has same length as input
    5. Finite values: All normal, subnormal, and zero values return false
-/
theorem isneginf_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isneginf x
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Primary property: result is true iff input is negative infinity
      (result[i] = ((x[i]).isInf ∧ (x[i]) < 0)) ∧
      -- Sanity checks: finite values return false
      (¬(x[i]).isInf → result[i] = false) ∧
      -- Positive infinity returns false
      ((x[i]).isInf ∧ (x[i]) > 0 → result[i] = false) ∧
      -- NaN is not negative infinity
      ((x[i]).isNaN → result[i] = false) ∧
      -- Zero is not negative infinity
      (x[i] = 0.0 → result[i] = false) ∧
      -- Mathematical property: if result is true, then x is infinite and negative
      (result[i] = true → (x[i]).isInf ∧ (x[i]) < 0) ∧
      -- Exclusivity: cannot be both negative infinity and NaN
      (result[i] = true → ¬(x[i]).isNaN)⌝⦄ := by
  simp [isneginf, isNegInf]
  intro i
  constructor
  · rfl
  constructor
  · intro h
    simp [h]
  constructor
  · intro h
    simp [h.1, h.2]
  constructor
  · intro h
    have : ¬(x[i]).isInf := by
      simp [Float.isNaN] at h
      exact Float.isNaN_not_isInf h
    simp [this]
  constructor
  · intro h
    have : ¬(x[i]).isInf := by
      simp [Float.isInf] at h
      exact Float.zero_not_isInf h
    simp [this]
  constructor
  · intro h
    exact h
  · intro h
    exact Float.isInf_not_isNaN h.1