import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.isposinf",
  "category": "Array contents testing",
  "description": "Test element-wise for positive infinity, return result as bool array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.isposinf.html",
  "doc": "Test element-wise for positive infinity, return result as bool array.\n\nParameters\n----------\nx : array_like\n    The input array.\nout : array_like, optional\n    A location into which the result is stored. If provided, it must have a\n    shape that the input broadcasts to. If not provided or None, a\n    freshly-allocated boolean array is returned.\n\nReturns\n-------\nout : ndarray\n    A boolean array with the same dimensions as the input.\n    If second argument is not supplied then a boolean array is returned\n    with values True where the corresponding element of the input is\n    positive infinity and values False where the element of the input\n    is not positive infinity.\n    \n    If a second argument is supplied the result is stored there. If the\n    type of that array is a numeric type the result is represented as\n    zeros and ones, if the type is boolean then as False and True.\n    The return value out is then a reference to that array.\n\nSee Also\n--------\nisinf, isneginf, isfinite, isnan\n\nNotes\n-----\nNumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic\n(IEEE 754).\n\nErrors result if the second argument is also supplied when x is a\nscalar input, if first and second arguments have different shapes,\nor if the first argument has complex values\n\nExamples\n--------\n>>> np.isposinf(np.PINF)\nTrue\n>>> np.isposinf(np.inf)\nTrue\n>>> np.isposinf(np.NINF)\nFalse\n>>> np.isposinf([-np.inf, 0., np.inf])\narray([False, False,  True])\n\n>>> x = np.array([-np.inf, 0., np.inf])\n>>> y = np.array([2, 2, 2])\n>>> np.isposinf(x, y)\narray([0, 0, 1])\n>>> y\narray([0, 0, 1])",
  "code": "def isposinf(x, out=None):\n    \"\"\"\n    Test element-wise for positive infinity, return result as bool array.\n    \n    Parameters\n    ----------\n    x : array_like\n        The input array.\n    out : array_like, optional\n        A location into which the result is stored. If provided, it must have a\n        shape that the input broadcasts to. If not provided or None, a\n        freshly-allocated boolean array is returned.\n    \n    Returns\n    -------\n    out : ndarray\n        A boolean array with the same dimensions as the input.\n        If second argument is not supplied then a boolean array is returned\n        with values True where the corresponding element of the input is\n        positive infinity and values False where the element of the input\n        is not positive infinity.\n        \n        If a second argument is supplied the result is stored there. If the\n        type of that array is a numeric type the result is represented as\n        zeros and ones, if the type is boolean then as False and True.\n        The return value `out` is then a reference to that array.\n    \n    See Also\n    --------\n    isinf, isneginf, isfinite, isnan\n    \n    Notes\n    -----\n    NumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic\n    (IEEE 754).\n    \n    Errors result if the second argument is also supplied when x is a\n    scalar input, if first and second arguments have different shapes,\n    or if the first argument has complex values\n    \n    Examples\n    --------\n    >>> np.isposinf(np.PINF)\n    True\n    >>> np.isposinf(np.inf)\n    True\n    >>> np.isposinf(np.NINF)\n    False\n    >>> np.isposinf([-np.inf, 0., np.inf])\n    array([False, False,  True])\n    \n    >>> x = np.array([-np.inf, 0., np.inf])\n    >>> y = np.array([2, 2, 2])\n    >>> np.isposinf(x, y)\n    array([0, 0, 1])\n    >>> y\n    array([0, 0, 1])\n    \n    \"\"\"\n    is_inf = nx.isinf(x)\n    try:\n        signbit = ~nx.signbit(x)\n    except TypeError as e:\n        dtype = nx.asanyarray(x).dtype\n        raise TypeError(f'This operation is not supported for {dtype} values '\n                        'because it would be ambiguous.') from e\n    else:\n        return nx.logical_and(is_inf, signbit, out)"
}
-/

-- LLM HELPER
def isPositiveInfinity (x : Float) : Bool :=
  x.isInf ∧ x > 0

/-- Test element-wise for positive infinity, return result as bool array -/
def isposinf {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  Id.mk (x.map isPositiveInfinity)

/-- Specification: isposinf returns True for positive infinity elements, False otherwise.
    
    This function tests each element according to IEEE 754 floating-point standard:
    - Returns true if the element is positive infinity (+∞)
    - Returns false for all other values including negative infinity, NaN, finite numbers, and zero
    
    Mathematical properties:
    1. Positive infinity detection: result[i] = true iff x[i] is positive infinity
    2. Distinction from negative infinity: only positive infinity returns true
    3. Distinction from NaN: positive infinity and NaN are mutually exclusive
    4. Result preserves shape: output vector has same length as input
    5. Finite values: All normal, subnormal, and zero values return false
-/
theorem isposinf_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isposinf x
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Primary property: result is true iff input is positive infinity
      (result.get i = ((x.get i).isInf ∧ (x.get i) > 0)) ∧
      -- Sanity checks: finite values return false
      (¬(x.get i).isInf → result.get i = false) ∧
      -- Negative infinity returns false
      ((x.get i).isInf ∧ (x.get i) < 0 → result.get i = false) ∧
      -- NaN is not positive infinity
      ((x.get i).isNaN → result.get i = false) ∧
      -- Zero is not positive infinity
      (x.get i = 0.0 → result.get i = false) ∧
      -- Mathematical property: if result is true, then x is infinite and positive
      (result.get i = true → (x.get i).isInf ∧ (x.get i) > 0) ∧
      -- Exclusivity: cannot be both positive infinity and NaN
      (result.get i = true → ¬(x.get i).isNaN)⌝⦄ := by
  unfold isposinf
  unfold wpHoare
  intro h
  constructor
  · simp [Id.mk]
  · intro result h_eq
    simp [Id.mk] at h_eq
    rw [← h_eq]
    intro i
    simp [Vector.get_map, isPositiveInfinity]
    constructor
    · rfl
    constructor
    · intro h_not_inf
      simp [h_not_inf]
    constructor
    · intro h_inf_neg
      simp [h_inf_neg.1, h_inf_neg.2]
    constructor
    · intro h_nan
      have h_not_inf : ¬(x.get i).isInf := by
        -- LLM HELPER
        have : (x.get i).isNaN → ¬(x.get i).isInf := by
          intro h_nan_inner
          exact Float.isNaN_not_isInf h_nan_inner
        exact this h_nan
      simp [h_not_inf]
    constructor
    · intro h_zero
      have h_not_inf : ¬(x.get i).isInf := by
        rw [h_zero]
        exact Float.zero_not_isInf
      simp [h_not_inf]
    constructor
    · intro h_true
      simp at h_true
      exact h_true
    · intro h_true
      simp at h_true
      -- LLM HELPER
      have : (x.get i).isInf → ¬(x.get i).isNaN := Float.isInf_not_isNaN
      exact this h_true.1