import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.linalg.norm",
  "category": "Norms and numbers",
  "description": "Matrix or vector norm",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.norm.html",
  "doc": "Matrix or vector norm.\n\nParameters:\n- x: Input array\n- ord: Order of the norm (see Notes)\n- axis: Axis along which to compute norms\n- keepdims: Keep dimensions for broadcasting\n\nCommon ord values:\n- None: 2-norm (default)\n- 'fro': Frobenius norm\n- 'nuc': Nuclear norm\n- inf: max(abs(x))\n- -inf: min(abs(x))\n- 1: max column sum (matrix) or sum(abs(x)) (vector)\n- 2: largest singular value (matrix) or 2-norm (vector)",
  "code": "\n\n@array_function_dispatch(_norm_dispatcher)\ndef norm(x, ord=None, axis=None, keepdims=False):\n    \"\"\"\n    Matrix or vector norm.\n\n    This function is able to return one of eight different matrix norms,\n    or one of an infinite number of vector norms (described below), depending\n    on the value of the ``ord`` parameter.\n\n    Parameters\n    ----------\n    x : array_like\n        Input array.  If `axis` is None, `x` must be 1-D or 2-D, unless `ord`\n        is None. If both `axis` and `ord` are None, the 2-norm of\n        ``x.ravel`` will be returned.\n    ord : {int, float, inf, -inf, 'fro', 'nuc'}, optional\n        Order of the norm (see table under ``Notes`` for what values are\n        supported for matrices and vectors respectively). inf means numpy's\n        `inf` object. The default is None.\n    axis : {None, int, 2-tuple of ints}, optional.\n        If `axis` is an integer, it specifies the axis of `x` along which to\n        compute the vector norms.  If `axis` is a 2-tuple, it specifies the\n        axes that hold 2-D matrices, and the matrix norms of these matrices\n        are computed.  If `axis` is None then either a vector norm (when `x`\n        is 1-D) or a matrix norm (when `x` is 2-D) is returned. The default\n        is None.\n\n    keepdims : bool, optional\n        If this is set to True, the axes which are normed over are left in the\n        result as dimensions with size one.  With this option the result will\n        broadcast correctly against the original `x`.\n\n    Returns\n    -------\n    n : float or ndarray\n        Norm of the matrix or vector(s).\n\n    See Also\n    --------\n    scipy.linalg.norm : Similar function in SciPy.\n\n    Notes\n    -----\n    For values of ``ord < 1``, the result is, strictly speaking, not a\n    mathematical 'norm', but it may still be useful for various numerical\n    purposes.\n\n    The following norms can be calculated:\n\n    =====  ============================  ==========================\n    ord    norm for matrices             norm for vectors\n    =====  ============================  ==========================\n    None   Frobenius norm                2-norm\n    'fro'  Frobenius norm                --\n    'nuc'  nuclear norm                  --\n    inf    max(sum(abs(x), axis=1))      max(abs(x))\n    -inf   min(sum(abs(x), axis=1))      min(abs(x))\n    0      --                            sum(x != 0)\n    1      max(sum(abs(x), axis=0))      as below\n    -1     min(sum(abs(x), axis=0))      as below\n    2      2-norm (largest sing. value)  as below\n    -2     smallest singular value       as below\n    other  --                            sum(abs(x)**ord)**(1./ord)\n    =====  ============================  ==========================\n\n    The Frobenius norm is given by [1]_:\n\n    :math:`||A||_F = [\\sum_{i,j} abs(a_{i,j})^2]^{1/2}`\n\n    The nuclear norm is the sum of the singular values.\n\n    Both the Frobenius and nuclear norm orders are only defined for\n    matrices and raise a ValueError when ``x.ndim != 2``.\n\n    References\n    ----------\n    .. [1] G. H. Golub and C. F. Van Loan, *Matrix Computations*,\n           Baltimore, MD, Johns Hopkins University Press, 1985, pg. 15\n\n    Examples\n    --------\n\n    >>> import numpy as np\n    >>> from numpy import linalg as LA\n    >>> a = np.arange(9) - 4\n    >>> a\n    array([-4, -3, -2, ...,  2,  3,  4])\n    >>> b = a.reshape((3, 3))\n    >>> b\n    array([[-4, -3, -2],\n           [-1,  0,  1],\n           [ 2,  3,  4]])\n\n    >>> LA.norm(a)\n    7.745966692414834\n    >>> LA.norm(b)\n    7.745966692414834\n    >>> LA.norm(b, 'fro')\n    7.745966692414834\n    >>> LA.norm(a, np.inf)\n    4.0\n    >>> LA.norm(b, np.inf)\n    9.0\n    >>> LA.norm(a, -np.inf)\n    0.0\n    >>> LA.norm(b, -np.inf)\n    2.0\n\n    >>> LA.norm(a, 1)\n    20.0\n    >>> LA.norm(b, 1)\n    7.0\n    >>> LA.norm(a, -1)\n    -4.6566128774142013e-010\n    >>> LA.norm(b, -1)\n    6.0\n    >>> LA.norm(a, 2)\n    7.745966692414834\n    >>> LA.norm(b, 2)\n    7.3484692283495345\n\n    >>> LA.norm(a, -2)\n    0.0\n    >>> LA.norm(b, -2)\n    1.8570331885190563e-016 # may vary\n    >>> LA.norm(a, 3)\n    5.8480354764257312 # may vary\n    >>> LA.norm(a, -3)\n    0.0\n\n    Using the `axis` argument to compute vector norms:\n\n    >>> c = np.array([[ 1, 2, 3],\n    ...               [-1, 1, 4]])\n    >>> LA.norm(c, axis=0)\n    array([ 1.41421356,  2.23606798,  5.        ])\n    >>> LA.norm(c, axis=1)\n    array([ 3.74165739,  4.24264069])\n    >>> LA.norm(c, ord=1, axis=1)\n    array([ 6.,  6.])\n\n    Using the `axis` argument to compute matrix norms:\n\n    >>> m = np.arange(8).reshape(2,2,2)\n    >>> LA.norm(m, axis=(1,2))\n    array([  3.74165739,  11.22497216])\n    >>> LA.norm(m[0, :, :]), LA.norm(m[1, :, :])\n    (3.7416573867739413, 11.224972160321824)\n\n    \"\"\"\n    x = asarray(x)\n\n    if not issubclass(x.dtype.type, (inexact, object_)):\n        x = x.astype(float)\n\n    # Immediately handle some default, simple, fast, and common cases.\n    if axis is None:\n        ndim = x.ndim\n        if (\n            (ord is None) or\n            (ord in ('f', 'fro') and ndim == 2) or\n            (ord == 2 and ndim == 1)\n        ):\n            x = x.ravel(order='K')\n            if isComplexType(x.dtype.type):\n                x_real = x.real\n                x_imag = x.imag\n                sqnorm = x_real.dot(x_real) + x_imag.dot(x_imag)\n            else:\n                sqnorm = x.dot(x)\n            ret = sqrt(sqnorm)\n            if keepdims:\n                ret = ret.reshape(ndim * [1])\n            return ret\n\n    # Normalize the `axis` argument to a tuple.\n    nd = x.ndim\n    if axis is None:\n        axis = tuple(range(nd))\n    elif not isinstance(axis, tuple):\n        try:\n            axis = int(axis)\n        except Exception as e:\n            raise TypeError(\n                \"'axis' must be None, an integer or a tuple of integers\"\n            ) from e\n        axis = (axis,)\n\n    if len(axis) == 1:\n        if ord == inf:\n            return abs(x).max(axis=axis, keepdims=keepdims, initial=0)\n        elif ord == -inf:\n            return abs(x).min(axis=axis, keepdims=keepdims)\n        elif ord == 0:\n            # Zero norm\n            return (\n                (x != 0)\n                .astype(x.real.dtype)\n                .sum(axis=axis, keepdims=keepdims)\n            )\n        elif ord == 1:\n            # special case for speedup\n            return add.reduce(abs(x), axis=axis, keepdims=keepdims)\n        elif ord is None or ord == 2:\n            # special case for speedup\n            s = (x.conj() * x).real\n            return sqrt(add.reduce(s, axis=axis, keepdims=keepdims))\n        # None of the str-type keywords for ord ('fro', 'nuc')\n        # are valid for vectors\n        elif isinstance(ord, str):\n            raise ValueError(f\"Invalid norm order '{ord}' for vectors\")\n        else:\n            absx = abs(x)\n            absx **= ord\n            ret = add.reduce(absx, axis=axis, keepdims=keepdims)\n            ret **= reciprocal(ord, dtype=ret.dtype)\n            return ret\n    elif len(axis) == 2:\n        row_axis, col_axis = axis\n        row_axis = normalize_axis_index(row_axis, nd)\n        col_axis = normalize_axis_index(col_axis, nd)\n        if row_axis == col_axis:\n            raise ValueError('Duplicate axes given.')\n        if ord == 2:\n            ret = _multi_svd_norm(x, row_axis, col_axis, amax, 0)\n        elif ord == -2:\n            ret = _multi_svd_norm(x, row_axis, col_axis, amin)\n        elif ord == 1:\n            if col_axis > row_axis:\n                col_axis -= 1\n            ret = add.reduce(abs(x), axis=row_axis).max(axis=col_axis, initial=0)\n        elif ord == inf:\n            if row_axis > col_axis:\n                row_axis -= 1\n            ret = add.reduce(abs(x), axis=col_axis).max(axis=row_axis, initial=0)\n        elif ord == -1:\n            if col_axis > row_axis:\n                col_axis -= 1\n            ret = add.reduce(abs(x), axis=row_axis).min(axis=col_axis)\n        elif ord == -inf:\n            if row_axis > col_axis:\n                row_axis -= 1\n            ret = add.reduce(abs(x), axis=col_axis).min(axis=row_axis)\n        elif ord in [None, 'fro', 'f']:\n            ret = sqrt(add.reduce((x.conj() * x).real, axis=axis))\n        elif ord == 'nuc':\n            ret = _multi_svd_norm(x, row_axis, col_axis, sum, 0)\n        else:\n            raise ValueError(\"Invalid norm order for matrices.\")\n        if keepdims:\n            ret_shape = list(x.shape)\n            ret_shape[axis[0]] = 1\n            ret_shape[axis[1]] = 1\n            ret = ret.reshape(ret_shape)\n        return ret\n    else:\n        raise ValueError(\"Improper number of dimensions to norm.\")"
}
-/

-- LLM HELPER
def sum_squares {n : Nat} (x : Vector Float n) : Float :=
  List.sum (x.toList.map (fun xi => xi * xi))

/-- numpy.linalg.norm: Compute the 2-norm (Euclidean norm) of a vector.
    
    This is the default vector norm when ord=None. For a vector x,
    the 2-norm is defined as: ||x||_2 = sqrt(sum(x[i]^2))
    
    This implementation focuses on the most common use case: computing
    the Euclidean norm of a 1D vector.
-/
def norm {n : Nat} (x : Vector Float n) : Id Float :=
  Float.sqrt (sum_squares x)

-- LLM HELPER
lemma all_zero_iff_sum_squares_zero {n : Nat} (x : Vector Float n) :
    (∀ i : Fin n, x.get i = 0) ↔ sum_squares x = 0 := by
  constructor
  · intro h
    simp [sum_squares]
    have : x.toList.map (fun xi => xi * xi) = List.replicate n 0 := by
      rw [List.eq_replicate]
      constructor
      · simp [Vector.toList_length]
      · intro xi hxi
        simp [Vector.toList] at hxi
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_get.mp hxi
        simp [h i]
    rw [this]
    simp
  · intro h
    intro i
    by_contra hne
    have : x.get i * x.get i > 0 := by
      apply mul_self_pos
      exact hne
    have : x.get i * x.get i ∈ x.toList.map (fun xi => xi * xi) := by
      simp [Vector.toList]
      use i
    have : List.sum (x.toList.map (fun xi => xi * xi)) > 0 := by
      apply List.sum_pos_of_pos_of_mem this
      exact this
    rw [h] at this
    exact lt_irrefl 0 this

/-- Specification: norm computes the Euclidean norm (2-norm) of a vector.
    
    The 2-norm is defined as the square root of the sum of squares of all elements.
    This is the most common vector norm used in numerical computing and is the
    default norm in NumPy when ord=None.
    
    Mathematical definition:
    - For a vector x = [x₁, x₂, ..., xₙ], the 2-norm is: ||x||₂ = √(Σᵢ xᵢ²)
    
    Key properties verified:
    1. Definition: result equals sqrt of sum of squared elements
    2. Non-negativity: norm(x) ≥ 0 for all x
    3. Definiteness: norm(x) = 0 if and only if x is the zero vector
    4. Empty vector: norm of empty vector is 0
    
    Note: Properties like triangle inequality and homogeneity follow from
    the definition but are not explicitly stated in this specification.
-/
theorem norm_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    norm x
    ⦃⇓result => ⌜result = Float.sqrt (List.sum (x.toList.map (fun xi => xi * xi))) ∧
                 result ≥ 0 ∧
                 (result = 0 ↔ ∀ i : Fin n, x.get i = 0) ∧
                 (n = 0 → result = 0)⌝⦄ := by
  simp [norm, sum_squares]
  constructor
  · rfl
  constructor
  · apply Float.sqrt_nonneg
  constructor
  · constructor
    · intro h
      rw [all_zero_iff_sum_squares_zero]
      rw [Float.sqrt_eq_zero_iff] at h
      exact h
    · intro h
      rw [all_zero_iff_sum_squares_zero] at h
      rw [Float.sqrt_eq_zero_iff]
      exact h
  · intro h
    simp [h]
    simp [Vector.toList_length]
    rfl