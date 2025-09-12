import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.take",
  "category": "Basic indexing",
  "description": "Take elements from an array along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.take.html",
  "doc": "Take elements from an array along an axis.\n\nWhen axis is not None, this function does the same thing as \"fancy\" indexing (indexing arrays using arrays); however, it can be easier to use if you need elements along a given axis.\n\nParameters\n----------\na : array_like (Ni..., M, Nk...)\n    The source array.\nindices : array_like (Nj...)\n    The indices of the values to extract.\n    Also allow scalars for indices.\naxis : int, optional\n    The axis over which to select values. By default, the flattened\n    input array is used.\nout : ndarray, optional (Ni..., Nj..., Nk...)\n    If provided, the result will be placed in this array.\nmode : {'raise', 'wrap', 'clip'}, optional\n    Specifies how out-of-bounds indices will behave.\n\nReturns\n-------\nout : ndarray (Ni..., Nj..., Nk...)\n    The returned array has the same type as \`a\`.\n\nExamples\n--------\n>>> import numpy as np\n>>> a = [4, 3, 5, 7, 6, 8]\n>>> indices = [0, 1, 4]\n>>> np.take(a, indices)\narray([4, 3, 6])",
  "code": "@array_function_dispatch(_take_dispatcher)\ndef take(a, indices, axis=None, out=None, mode='raise'):\n    \"\"\"\n    Take elements from an array along an axis.\n\n    When axis is not None, this function does the same thing as \"fancy\"\n    indexing (indexing arrays using arrays); however, it can be easier to use\n    if you need elements along a given axis.\n\n    Parameters\n    ----------\n    a : array_like (Ni..., M, Nk...)\n        The source array.\n    indices : array_like (Nj...)\n        The indices of the values to extract.\n        Also allow scalars for indices.\n    axis : int, optional\n        The axis over which to select values. By default, the flattened\n        input array is used.\n    out : ndarray, optional (Ni..., Nj..., Nk...)\n        If provided, the result will be placed in this array.\n    mode : {'raise', 'wrap', 'clip'}, optional\n        Specifies how out-of-bounds indices will behave.\n\n    Returns\n    -------\n    out : ndarray (Ni..., Nj..., Nk...)\n        The returned array has the same type as \`a\`.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> a = [4, 3, 5, 7, 6, 8]\n    >>> indices = [0, 1, 4]\n    >>> np.take(a, indices)\n    array([4, 3, 6])\n    \"\"\"\n    return _wrapfunc(a, 'take', indices, axis=axis, out=out, mode=mode)"
}
-/

open Std.Do

/-- Take elements from a source array at specified indices.
    Given a source array 'arr' and a vector of indices 'indices',
    returns a new array containing the elements from 'arr' at the positions
    specified by 'indices'. The indices must be valid positions in the source array.
    
    This is a simplified 1D version of numpy.take with 'raise' mode,
    where all indices must be valid (in range [0, n-1]). -/
def take {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) : Id (Vector Float m) :=
  sorry

/-- Specification: take extracts elements from a source array at specified indices.
    
    Mathematical properties:
    1. The result has the same length as the indices array
    2. For each position i in the result, result[i] = arr[indices[i]]
    3. All indices must be valid (enforced by Fin type)
    4. The order of elements in the result follows the order of indices
    5. The same index can appear multiple times, resulting in duplicated elements
    
    The function implements: result[i] = arr.get (indices.get i)
    
    This captures the core behavior of numpy.take in 'raise' mode where indices
    must be in valid range. The use of Fin type ensures type safety and eliminates
    the need for runtime bounds checking. The result preserves the element type
    of the source array. -/
theorem take_spec {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) :
    ⦃⌜True⌝⦄
    take arr indices
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = arr.get (indices.get i)⌝⦄ := by
  sorry
