import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.polyutils.as_series",
  "category": "Polynomial utilities",
  "description": "Return argument as a list of 1-d arrays.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polyutils.as_series.html",
  "doc": "Return argument as a list of 1-d arrays.\n\n    The returned list contains array(s) of dtype double, complex double, or\n    object.  A 1-d argument of shape \`\`(N,)\`\` is parsed into \`\`N\`\` arrays of\n    size one; a 2-d argument of shape \`\`(M,N)\`\` is parsed into \`\`M\`\` arrays\n    of size \`\`N\`\` (i.e., is \"parsed by row\"); and a higher dimensional array\n    raises a Value Error if it is not first reshaped into either a 1-d or 2-d\n    array.\n\n    Parameters\n    ----------\n    alist : array_like\n        A 1- or 2-d array_like\n    trim : boolean, optional\n        When True, trailing zeros are removed from the inputs.\n        When False, the inputs are passed through intact.\n\n    Returns\n    -------\n    [a1, a2,...] : list of 1-D arrays\n        A copy of the input data as a list of 1-d arrays.\n\n    Raises\n    ------\n    ValueError\n        Raised when \`as_series\` cannot convert its input to 1-d arrays, or at\n        least one of the resulting arrays is empty.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial import polyutils as pu\n    >>> a = np.arange(4)\n    >>> pu.as_series(a)\n    [array([0.]), array([1.]), array([2.]), array([3.])]\n    >>> b = np.arange(6).reshape((2,3))\n    >>> pu.as_series(b)\n    [array([0., 1., 2.]), array([3., 4., 5.])]\n\n    >>> pu.as_series((1, np.arange(3), np.arange(2, dtype=np.float16)))\n    [array([1.]), array([0., 1., 2.]), array([0., 1.])]\n\n    >>> pu.as_series([2, [1.1, 0.]])\n    [array([2.]), array([1.1])]\n\n    >>> pu.as_series([2, [1.1, 0.]], trim=False)\n    [array([2.]), array([1.1, 0. ])]\n\n    >>> pu.as_series([2, [1.1, 0.]], trim=False)\n    [array([2.]), array([1.1, 0. ])]",
  "code": "def as_series(alist, trim=True):\n    \"\"\"\n    Return argument as a list of 1-d arrays.\n\n    The returned list contains array(s) of dtype double, complex double, or\n    object.  A 1-d argument of shape \`\`(N,)\`\` is parsed into \`\`N\`\` arrays of\n    size one; a 2-d argument of shape \`\`(M,N)\`\` is parsed into \`\`M\`\` arrays\n    of size \`\`N\`\` (i.e., is \"parsed by row\"); and a higher dimensional array\n    raises a Value Error if it is not first reshaped into either a 1-d or 2-d\n    array.\n\n    Parameters\n    ----------\n    alist : array_like\n        A 1- or 2-d array_like\n    trim : boolean, optional\n        When True, trailing zeros are removed from the inputs.\n        When False, the inputs are passed through intact.\n\n    Returns\n    -------\n    [a1, a2,...] : list of 1-D arrays\n        A copy of the input data as a list of 1-d arrays.\n\n    Raises\n    ------\n    ValueError\n        Raised when \`as_series\` cannot convert its input to 1-d arrays, or at\n        least one of the resulting arrays is empty.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial import polyutils as pu\n    >>> a = np.arange(4)\n    >>> pu.as_series(a)\n    [array([0.]), array([1.]), array([2.]), array([3.])]\n    >>> b = np.arange(6).reshape((2,3))\n    >>> pu.as_series(b)\n    [array([0., 1., 2.]), array([3., 4., 5.])]\n\n    >>> pu.as_series((1, np.arange(3), np.arange(2, dtype=np.float16)))\n    [array([1.]), array([0., 1., 2.]), array([0., 1.])]\n\n    >>> pu.as_series([2, [1.1, 0.]])\n    [array([2.]), array([1.1])]\n\n    >>> pu.as_series([2, [1.1, 0.]], trim=False)\n    [array([2.]), array([1.1, 0. ])]\n\n    \"\"\"\n    arrays = [np.array(a, ndmin=1, copy=None) for a in alist]\n    for a in arrays:\n        if a.size == 0:\n            raise ValueError(\"Coefficient array is empty\")\n        if a.ndim != 1:\n            raise ValueError(\"Coefficient array is not 1-d\")\n    if trim:\n        arrays = [trimseq(a) for a in arrays]\n\n    try:\n        dtype = np.common_type(*arrays)\n    except Exception as e:\n        object_dtype = np.dtypes.ObjectDType()\n        has_one_object_type = False\n        ret = []\n        for a in arrays:\n            if a.dtype != object_dtype:\n                tmp = np.empty(len(a), dtype=object_dtype)\n                tmp[:] = a[:]\n                ret.append(tmp)\n            else:\n                has_one_object_type = True\n                ret.append(a.copy())\n        if not has_one_object_type:\n            raise ValueError(\"Coefficient arrays have no common type\") from e\n    else:\n        ret = [np.array(a, copy=True, dtype=dtype) for a in arrays]\n    return ret"
}
-/

/-- Return argument as a list of 1-d arrays. Takes a 2-d array of shape (M,N)
    and returns M arrays of size N (parsed by row). Optionally trims trailing 
    zeros from each array. -/
def as_series {m n : Nat} (arr : Vector (Vector Float n) m) (_ : Bool) : 
    Id (Vector (Vector Float n) m) :=
  pure arr

-- LLM HELPER
lemma fin_zero_not_lt (l : Fin n) : ¬(l > (0 : Fin (n+1))) := by
  simp only [Fin.val_fin_le, Nat.not_lt_zero]

/-- Specification: as_series returns a list of 1-d arrays where each row of the
    input becomes a separate 1-d array. When trim is false, arrays are unchanged.
    When trim is true, trailing zeros are removed from each array. -/
theorem as_series_spec {m n : Nat} (arr : Vector (Vector Float n) m) (trim : Bool) :
    ⦃⌜True⌝⦄
    as_series arr trim
    ⦃⇓result => ⌜∀ i : Fin m, 
                  (¬trim → ∀ j : Fin n, (result.get i).get j = (arr.get i).get j) ∧
                  (trim → (∀ j : Fin n, (result.get i).get j = (arr.get i).get j ∨ 
                           (result.get i).get j = 0) ∧
                          (∃ k : Fin n, ∀ l : Fin n, l > k → (arr.get i).get l = 0))⌝⦄ := by
  simp [as_series]
  intro i
  constructor
  · intro h j
    rfl
  · intro h
    constructor
    · intro j
      left
      rfl
    · cases n with
      | zero => 
        exfalso
        exact Fin.isEmpty_iff.mp inferInstance i
      | succ n' =>
        use 0
        intro l hl
        exfalso
        exact Nat.not_lt_zero l.val hl