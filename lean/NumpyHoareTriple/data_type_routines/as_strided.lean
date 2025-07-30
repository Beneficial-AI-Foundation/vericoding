import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.as_strided",
  "category": "Memory and Striding",
  "description": "Create a view into the array with the given shape and strides",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.lib.stride_tricks.as_strided.html",
  "doc": "Create a view into the array with the given shape and strides.\n\nWarning: This function has to be used with extreme care, see notes.\n\nParameters\n----------\nx : ndarray\n    Array to create a new view for.\nshape : sequence of int, optional\n    The shape of the new array. Defaults to x.shape.\nstrides : sequence of int, optional\n    The strides of the new array. Defaults to x.strides.\nsubok : bool, optional\n    If True, subclasses are preserved.\nwriteable : bool, optional\n    If set to False, the returned array will always be readonly.\n\nReturns\n-------\nview : ndarray\n\nNotes\n-----\nas_strided creates a view into the array given the exact strides and shape. This means it manipulates the internal data structure of ndarray and, if done incorrectly, the array elements can point to invalid memory and can corrupt results or crash your program.\n\nExamples\n--------\n>>> x = np.array([1, 2, 3, 4, 5])\n>>> np.lib.stride_tricks.as_strided(x, shape=(3,), strides=(8,))\narray([1, 2, 3])",
  "code": "\ndef as_strided(x, shape=None, strides=None, subok=False, writeable=True):\n    \"\"\"\n    Create a view into the array with the given shape and strides.\n\n    .. warning:: This function has to be used with extreme care, see notes.\n\n    Parameters\n    ----------\n    x : ndarray\n        Array to create a new view for.\n    shape : sequence of int, optional\n        The shape of the new array. Defaults to \`\`x.shape\`\`.\n    strides : sequence of int, optional\n        The strides of the new array. Defaults to \`\`x.strides\`\`.\n    subok : bool, optional\n        .. versionadded:: 1.10\n\n        If True, subclasses are preserved.\n    writeable : bool, optional\n        .. versionadded:: 1.12\n\n        If set to False, the returned array will always be readonly.\n        Otherwise it will be writable if the original array was. It\n        is advisable to set this to False if possible (see Notes).\n\n    Returns\n    -------\n    view : ndarray\n\n    See also\n    --------\n    ndarray.strides : The array's strides.\n    ndarray.shape : The array's shape.\n    broadcast_to : broadcast an array to a given shape.\n    reshape : reshape an array.\n    lib.index_tricks.sliding_window_view :\n        userfriendly and safe function for rolling window views.\n\n    Notes\n    -----\n    \`\`as_strided\`\` creates a view into the array given the exact strides\n    and shape. This means it manipulates the internal data structure of\n    ndarray and, if done incorrectly, the array elements can point to\n    invalid memory and can corrupt results or crash your program.\n    It is advisable to always use the original \`\`x.strides\`\` when\n    calculating new strides to avoid reliance on a contiguous memory\n    layout.\n\n    Furthermore, arrays created with this function often contain self\n    overlapping memory, so that two elements are identical.\n    Vectorized write operations on such arrays will typically be\n    unpredictable. They may even give different results for small, large,\n    or transposed arrays.\n    Since writing to these arrays has to be tested and done with great\n    care, you may want to use \`\`writeable=False\`\` to avoid accidental write\n    operations.\n\n    For these reasons it is advisable to avoid \`\`as_strided\`\` when\n    possible.\n    \"\"\"\n    # first convert input to array, possibly keeping subclass\n    x = np.array(x, copy=None, subok=subok)\n    interface = dict(x.__array_interface__)\n    if shape is not None:\n        interface['shape'] = tuple(shape)\n    if strides is not None:\n        interface['strides'] = tuple(strides)\n\n    array = np.asarray(DummyArray(interface, base=x))\n    # The array interface should ensure that the array is already in\n    # exactly the state we want, but check just in case...\n    # 2022-07-08 1.24.0.dev0+236.g86ba6cc1f7\n    # assert array.dtype == x.dtype\n    # Since dtype is not part of the interface, it may have gotten\n    # lost in the np.asarray call above. Explicitly re-assign it\n    # as a workaround.\n    # See: https://github.com/numpy/numpy/issues/21871\n    array.dtype = x.dtype\n\n    view = _maybe_view_as_subclass(x, array)\n\n    if view.flags.writeable and not writeable:\n        view.flags.writeable = False\n\n    return view"
}
-/

open Std.Do

/-- numpy.as_strided: Create a view into the array with the given shape and strides.
    
    Creates a new view of an array with specified shape and strides.
    This is a simplified version that focuses on the core mathematical
    property: creating a view with a different shape but accessing
    elements from the original array based on stride patterns.
    
    For safety, we restrict to cases where the new shape is smaller
    than or equal to the original array size.
-/
def numpy_as_strided {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) : Id (Vector Float m) :=
  sorry

/-- Specification: numpy.as_strided creates a view with specified strides.
    
    Precondition: The strided access must be valid (m * stride ≤ n)
    Postcondition: Each element in the result is taken from the original
    array at positions determined by the stride pattern.
    
    For element i in the result, it equals x[i * stride].
-/
theorem numpy_as_strided_spec {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) :
    ⦃⌜m * stride ≤ n ∧ stride > 0⌝⦄
    numpy_as_strided x stride h_valid h_stride_pos
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = x.get ⟨i.val * stride, 
                   by have h1 : i.val < m := i.isLt
                      have h2 : i.val * stride < m * stride := by
                        apply Nat.mul_lt_mul_of_pos_right h1 h_stride_pos
                      exact Nat.lt_of_lt_of_le h2 h_valid⟩⌝⦄ := by
  sorry