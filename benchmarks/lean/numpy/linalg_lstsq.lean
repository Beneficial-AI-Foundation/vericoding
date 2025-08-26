import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.linalg.lstsq",
  "category": "Solving equations and inverting matrices",
  "description": "Return the least-squares solution to a linear matrix equation",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.lstsq.html",
  "doc": "Return the least-squares solution to a linear matrix equation.\n\nSolves the equation a @ x = b by minimizing ||b - ax||^2.\n\nParameters:\n- a: Coefficient matrix (M, N)\n- b: Ordinate values (M,) or (M, K)\n- rcond: Cut-off ratio for small singular values\n\nReturns tuple of:\n- x: Least-squares solution\n- residuals: Sums of squared residuals\n- rank: Rank of matrix a\n- s: Singular values of a",
  "code": "\n\n@array_function_dispatch(_lstsq_dispatcher)\ndef lstsq(a, b, rcond=None):\n    r\"\"\"\n    Return the least-squares solution to a linear matrix equation.\n\n    Computes the vector \`x\` that approximately solves the equation\n    \`\`a @ x = b\`\`. The equation may be under-, well-, or over-determined\n    (i.e., the number of linearly independent rows of \`a\` can be less than,\n    equal to, or greater than its number of linearly independent columns).\n    If \`a\` is square and of full rank, then \`x\` (but for round-off error)\n    is the \"exact\" solution of the equation. Else, \`x\` minimizes the\n    Euclidean 2-norm :math:\`||b - ax||\`. If there are multiple minimizing\n    solutions, the one with the smallest 2-norm :math:\`||x||\` is returned.\n\n    Parameters\n    ----------\n    a : (M, N) array_like\n        \"Coefficient\" matrix.\n    b : {(M,), (M, K)} array_like\n        Ordinate or \"dependent variable\" values. If \`b\` is two-dimensional,\n        the least-squares solution is calculated for each of the \`K\` columns\n        of \`b\`.\n    rcond : float, optional\n        Cut-off ratio for small singular values of \`a\`.\n        For the purposes of rank determination, singular values are treated\n        as zero if they are smaller than \`rcond\` times the largest singular\n        value of \`a\`.\n        The default uses the machine precision times \`\`max(M, N)\`\`.  Passing\n        \`\`-1\`\` will use machine precision.\n\n        .. versionchanged:: 2.0\n            Previously, the default was \`\`-1\`\`, but a warning was given that\n            this would change.\n\n    Returns\n    -------\n    x : {(N,), (N, K)} ndarray\n        Least-squares solution. If \`b\` is two-dimensional,\n        the solutions are in the \`K\` columns of \`x\`.\n    residuals : {(1,), (K,), (0,)} ndarray\n        Sums of squared residuals: Squared Euclidean 2-norm for each column in\n        \`\`b - a @ x\`\`.\n        If the rank of \`a\` is < N or M <= N, this is an empty array.\n        If \`b\` is 1-dimensional, this is a (1,) shape array.\n        Otherwise the shape is (K,).\n    rank : int\n        Rank of matrix \`a\`.\n    s : (min(M, N),) ndarray\n        Singular values of \`a\`.\n\n    Raises\n    ------\n    LinAlgError\n        If computation does not converge.\n\n    See Also\n    --------\n    scipy.linalg.lstsq : Similar function in SciPy.\n\n    Notes\n    -----\n    If \`b\` is a matrix, then all array results are returned as matrices.\n\n    Examples\n    --------\n    Fit a line, \`\`y = mx + c\`\`, through some noisy data-points:\n\n    >>> import numpy as np\n    >>> x = np.array([0, 1, 2, 3])\n    >>> y = np.array([-1, 0.2, 0.9, 2.1])\n\n    By examining the coefficients, we see that the line should have a\n    gradient of roughly 1 and cut the y-axis at, more or less, -1.\n\n    We can rewrite the line equation as \`\`y = Ap\`\`, where \`\`A = [[x 1]]\`\`\n    and \`\`p = [[m], [c]]\`\`.  Now use \`lstsq\` to solve for \`p\`:\n\n    >>> A = np.vstack([x, np.ones(len(x))]).T\n    >>> A\n    array([[ 0.,  1.],\n           [ 1.,  1.],\n           [ 2.,  1.],\n           [ 3.,  1.]])\n\n    >>> m, c = np.linalg.lstsq(A, y)[0]\n    >>> m, c\n    (1.0 -0.95) # may vary\n\n    Plot the data along with the fitted line:\n\n    >>> import matplotlib.pyplot as plt\n    >>> _ = plt.plot(x, y, 'o', label='Original data', markersize=10)\n    >>> _ = plt.plot(x, m*x + c, 'r', label='Fitted line')\n    >>> _ = plt.legend()\n    >>> plt.show()\n\n    \"\"\"\n    a, _ = _makearray(a)\n    b, wrap = _makearray(b)\n    is_1d = b.ndim == 1\n    if is_1d:\n        b = b[:, newaxis]\n    _assert_2d(a, b)\n    m, n = a.shape[-2:]\n    m2, n_rhs = b.shape[-2:]\n    if m != m2:\n        raise LinAlgError('Incompatible dimensions')\n\n    t, result_t = _commonType(a, b)\n    result_real_t = _realType(result_t)\n\n    if rcond is None:\n        rcond = finfo(t).eps * max(n, m)\n\n    signature = 'DDd->Ddid' if isComplexType(t) else 'ddd->ddid'\n    if n_rhs == 0:\n        # lapack can't handle n_rhs = 0 - so allocate\n        # the array one larger in that axis\n        b = zeros(b.shape[:-2] + (m, n_rhs + 1), dtype=b.dtype)\n\n    with errstate(call=_raise_linalgerror_lstsq, invalid='call',\n                  over='ignore', divide='ignore', under='ignore'):\n        x, resids, rank, s = _umath_linalg.lstsq(a, b, rcond,\n                                                 signature=signature)\n    if m == 0:\n        x[...] = 0\n    if n_rhs == 0:\n        # remove the item we added\n        x = x[..., :n_rhs]\n        resids = resids[..., :n_rhs]\n\n    # remove the axis we added\n    if is_1d:\n        x = x.squeeze(axis=-1)\n        # we probably should squeeze resids too, but we can't\n        # without breaking compatibility.\n\n    # as documented\n    if rank != n or m <= n:\n        resids = array([], result_real_t)\n\n    # coerce output arrays\n    s = s.astype(result_real_t, copy=False)\n    resids = resids.astype(result_real_t, copy=False)\n    # Copying lets the memory in r_parts be freed\n    x = x.astype(result_t, copy=True)\n    return wrap(x), wrap(resids), rank, s"
}
-/

open Std.Do

/-- Helper function to compute dot product of two vectors -/
def dotProduct {n : Nat} (u v : Vector Float n) : Float := by
  induction n with
  | zero => exact 0
  | succ k ih => 
    exact (u.get ⟨0, Nat.zero_lt_succ k⟩) * (v.get ⟨0, Nat.zero_lt_succ k⟩) + 
          ih (u.tail) (v.tail)

/-- Matrix-vector multiplication for Vector types -/
def matVecMul {M N : Nat} (A : Vector (Vector Float N) M) (x : Vector Float N) : Vector Float M :=
  Vector.ofFn fun i => dotProduct (A.get i) x

/-- Euclidean norm squared of a vector -/
def normSq {n : Nat} (v : Vector Float n) : Float :=
  dotProduct v v

/-- Vector subtraction -/
def vecSub {n : Nat} (a b : Vector Float n) : Vector Float n :=
  Vector.ofFn fun i => a.get i - b.get i

/-- Return the least-squares solution to a linear matrix equation -/
def lstsq {M N : Nat} (a : Vector (Vector Float N) M) (b : Vector Float M) : 
    Id (Vector Float N) :=
  sorry

/-- Specification: lstsq returns the solution that minimizes ||b - a*x||^2 -/
theorem lstsq_spec {M N : Nat} (a : Vector (Vector Float N) M) (b : Vector Float M) 
    (h_dims : M > 0 ∧ N > 0) :
    ⦃⌜M > 0 ∧ N > 0⌝⦄
    lstsq a b
    ⦃⇓x => ⌜∀ y : Vector Float N, 
           normSq (vecSub b (matVecMul a x)) ≤ normSq (vecSub b (matVecMul a y))⌝⦄ := by
  sorry
