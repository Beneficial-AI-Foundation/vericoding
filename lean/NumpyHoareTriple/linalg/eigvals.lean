import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.linalg.eigvals",
  "category": "Matrix eigenvalues",
  "description": "Compute the eigenvalues of a general matrix",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.eigvals.html",
  "doc": "Compute the eigenvalues of a general matrix.\n\nMain difference from eig: Does not compute eigenvectors.\n\nParameters:\n- a: Square array\n\nReturns:\n- w: The eigenvalues, not necessarily ordered",
  "code": "\n\n@array_function_dispatch(_unary_dispatcher)\ndef eigvals(a):\n    \"\"\"\n    Compute the eigenvalues of a general matrix.\n\n    Main difference between \`eigvals\` and \`eig\`: the eigenvectors aren't\n    returned.\n\n    Parameters\n    ----------\n    a : (..., M, M) array_like\n        A complex- or real-valued matrix whose eigenvalues will be computed.\n\n    Returns\n    -------\n    w : (..., M,) ndarray\n        The eigenvalues, each repeated according to its multiplicity.\n        They are not necessarily ordered, nor are they necessarily\n        real for real matrices.\n\n    Raises\n    ------\n    LinAlgError\n        If the eigenvalue computation does not converge.\n\n    See Also\n    --------\n    eig : eigenvalues and right eigenvectors of general arrays\n    eigvalsh : eigenvalues of real symmetric or complex Hermitian\n               (conjugate symmetric) arrays.\n    eigh : eigenvalues and eigenvectors of real symmetric or complex\n           Hermitian (conjugate symmetric) arrays.\n    scipy.linalg.eigvals : Similar function in SciPy.\n\n    Notes\n    -----\n    Broadcasting rules apply, see the \`numpy.linalg\` documentation for\n    details.\n\n    This is implemented using the \`\`_geev\`\` LAPACK routines which compute\n    the eigenvalues and eigenvectors of general square arrays.\n\n    Examples\n    --------\n    Illustration, using the fact that the eigenvalues of a diagonal matrix\n    are its diagonal elements, that multiplying a matrix on the left\n    by an orthogonal matrix, \`Q\`, and on the right by \`Q.T\` (the transpose\n    of \`Q\`), preserves the eigenvalues of the \"middle\" matrix. In other words,\n    if \`Q\` is orthogonal, then \`\`Q * A * Q.T\`\` has the same eigenvalues as\n    \`\`A\`\`:\n\n    >>> import numpy as np\n    >>> from numpy import linalg as LA\n    >>> x = np.random.random()\n    >>> Q = np.array([[np.cos(x), -np.sin(x)], [np.sin(x), np.cos(x)]])\n    >>> LA.norm(Q[0, :]), LA.norm(Q[1, :]), np.dot(Q[0, :],Q[1, :])\n    (1.0, 1.0, 0.0)\n\n    Now multiply a diagonal matrix by \`\`Q\`\` on one side and\n    by \`\`Q.T\`\` on the other:\n\n    >>> D = np.diag((-1,1))\n    >>> LA.eigvals(D)\n    array([-1.,  1.])\n    >>> A = np.dot(Q, D)\n    >>> A = np.dot(A, Q.T)\n    >>> LA.eigvals(A)\n    array([ 1., -1.]) # random\n\n    \"\"\"\n    a, wrap = _makearray(a)\n    _assert_stacked_square(a)\n    _assert_finite(a)\n    t, result_t = _commonType(a)\n\n    signature = 'D->D' if isComplexType(t) else 'd->D'\n    with errstate(call=_raise_linalgerror_eigenvalues_nonconvergence,\n                  invalid='call', over='ignore', divide='ignore',\n                  under='ignore'):\n        w = _umath_linalg.eigvals(a, signature=signature)\n\n    if not isComplexType(t):\n        if all(w.imag == 0):\n            w = w.real\n            result_t = _realType(result_t)\n        else:\n            result_t = _complexType(result_t)\n\n    return w.astype(result_t, copy=False)"
}
-/

/-- Matrix represented as a vector of vectors (rows) -/
def Matrix (n : Nat) (α : Type) : Type := Vector (Vector α n) n

/-- Complex number type for eigenvalues -/
structure Complex where
  re : Float
  im : Float
  deriving Repr

/-- Compute the eigenvalues of a general square matrix -/
def eigvals {n : Nat} (a : Matrix (n + 1) Float) : Id (Vector Complex (n + 1)) :=
  sorry

/-- Specification: eigvals computes eigenvalues of a square matrix -/
theorem eigvals_spec {n : Nat} (a : Matrix (n + 1) Float) :
    ⦃⌜True⌝⦄
    eigvals a
    ⦃⇓w => ⌜-- The result contains exactly n+1 eigenvalues (guaranteed by type)
            -- For diagonal matrices, eigenvalues are the diagonal elements
            -- This captures the key mathematical property from the numpy documentation
            (∀ i j : Fin (n + 1), i ≠ j → (a.get i).get j = 0) →
            (∀ i : Fin (n + 1), ∃ j : Fin (n + 1), (w.get j).re = (a.get i).get i ∧ (w.get j).im = 0)⌝⦄ := by
  sorry