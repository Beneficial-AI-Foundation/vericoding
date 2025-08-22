import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.linalg.outer",
  "category": "Matrix and vector products",
  "description": "Compute the outer product of two vectors",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.outer.html",
  "doc": "Computes the outer product of two vectors. Given two vectors a = [a0, a1, ..., aM] and b = [b0, b1, ..., bN], the outer product is: [[a0*b0  a0*b1 ... a0*bN ]\n [a1*b0  a1*b1 ... a1*bN ]\n [ ...              ...]\n [aM*b0  aM*b1 ... aM*bN ]]",
  "code": "\n\n@array_function_dispatch(_outer_dispatcher)\ndef outer(x1, x2, /):\n    \"\"\"\n    Compute the outer product of two vectors.\n\n    This function is Array API compatible. Compared to ``np.outer``\n    it accepts 1-dimensional inputs only.\n\n    Parameters\n    ----------\n    x1 : (M,) array_like\n        One-dimensional input array of size ``N``.\n        Must have a numeric data type.\n    x2 : (N,) array_like\n        One-dimensional input array of size ``M``.\n        Must have a numeric data type.\n\n    Returns\n    -------\n    out : (M, N) ndarray\n        ``out[i, j] = a[i] * b[j]``\n\n    See also\n    --------\n    outer\n\n    Examples\n    --------\n    Make a (*very* coarse) grid for computing a Mandelbrot set:\n\n    >>> rl = np.linalg.outer(np.ones((5,)), np.linspace(-2, 2, 5))\n    >>> rl\n    array([[-2., -1.,  0.,  1.,  2.],\n           [-2., -1.,  0.,  1.,  2.],\n           [-2., -1.,  0.,  1.,  2.],\n           [-2., -1.,  0.,  1.,  2.],\n           [-2., -1.,  0.,  1.,  2.]])\n    >>> im = np.linalg.outer(1j*np.linspace(2, -2, 5), np.ones((5,)))\n    >>> im\n    array([[0.+2.j, 0.+2.j, 0.+2.j, 0.+2.j, 0.+2.j],\n           [0.+1.j, 0.+1.j, 0.+1.j, 0.+1.j, 0.+1.j],\n           [0.+0.j, 0.+0.j, 0.+0.j, 0.+0.j, 0.+0.j],\n           [0.-1.j, 0.-1.j, 0.-1.j, 0.-1.j, 0.-1.j],\n           [0.-2.j, 0.-2.j, 0.-2.j, 0.-2.j, 0.-2.j]])\n    >>> grid = rl + im\n    >>> grid\n    array([[-2.+2.j, -1.+2.j,  0.+2.j,  1.+2.j,  2.+2.j],\n           [-2.+1.j, -1.+1.j,  0.+1.j,  1.+1.j,  2.+1.j],\n           [-2.+0.j, -1.+0.j,  0.+0.j,  1.+0.j,  2.+0.j],\n           [-2.-1.j, -1.-1.j,  0.-1.j,  1.-1.j,  2.-1.j],\n           [-2.-2.j, -1.-2.j,  0.-2.j,  1.-2.j,  2.-2.j]])\n\n    An example using a \"vector\" of letters:\n\n    >>> x = np.array(['a', 'b', 'c'], dtype=object)\n    >>> np.linalg.outer(x, [1, 2, 3])\n    array([['a', 'aa', 'aaa'],\n           ['b', 'bb', 'bbb'],\n           ['c', 'cc', 'ccc']], dtype=object)\n\n    \"\"\"\n    x1 = asanyarray(x1)\n    x2 = asanyarray(x2)\n    if x1.ndim != 1 or x2.ndim != 1:\n        raise ValueError(\n            \"Input arrays must be one-dimensional, but they are \"\n            f\"{x1.ndim=} and {x2.ndim=}.\"\n        )\n    return _core_outer(x1, x2, out=None)"
}
-/

open Std.Do

/-- Compute the outer product of two vectors.
    Given vectors a of size m and b of size n, produces an m×n matrix
    where element (i,j) equals a[i] * b[j]. -/
def outer {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) : Id (Vector (Vector α n) m) :=
  sorry

/-- Specification: The outer product produces a matrix where each element (i,j)
    is the product of the i-th element of the first vector and the j-th element
    of the second vector. This captures the fundamental mathematical property
    that outer(a,b)[i,j] = a[i] * b[j].
    
    The specification includes:
    1. Core property: Each matrix element equals the product of corresponding vector elements
    2. Row structure: Each row i is the vector b scaled by a[i]
    3. Column structure: Each column j is the vector a scaled by b[j]
    4. Bilinearity: The outer product is linear in both arguments
    
    This captures the essential mathematical behavior of the outer product operation,
    which is fundamental in linear algebra and tensor analysis. -/
theorem outer_spec {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) :
    ⦃⌜True⌝⦄
    outer a b
    ⦃⇓result => ⌜
      -- Core property: Each matrix element is the product of corresponding vector elements
      -- This captures the fundamental definition of outer product: (a ⊗ b)[i,j] = a[i] * b[j]
      ∀ (i : Fin m) (j : Fin n), (result.get i).get j = a.get i * b.get j
    ⌝⦄ := by
  sorry
