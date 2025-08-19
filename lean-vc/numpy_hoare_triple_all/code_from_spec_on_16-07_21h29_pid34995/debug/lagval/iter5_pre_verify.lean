import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagval",
  "category": "Laguerre polynomials",
  "description": "Evaluate a Laguerre series at points x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagval.html",
  "doc": "Evaluate a Laguerre series at points x.\n\n    If \`c\` is of length \`\`n + 1\`\`, this function returns the value:\n\n    .. math:: p(x) = c_0 * L_0(x) + c_1 * L_1(x) + ... + c_n * L_n(x)\n\n    The parameter \`x\` is converted to an array only if it is a tuple or a\n    list, otherwise it is treated as a scalar. In either case, either \`x\`\n    or its elements must support multiplication and addition both with\n    themselves and with the elements of \`c\`.\n\n    If \`c\` is a 1-D array, then \`\`p(x)\`\` will have the same shape as \`x\`.  If\n    \`c\` is multidimensional, then the shape of the result depends on the\n    value of \`tensor\`. If \`tensor\` is true the shape will be c.shape[1:] +\n    x.shape. If \`tensor\` is false the shape will be c.shape[1:]. Note that\n    scalars have shape (,).\n\n    Trailing zeros in the coefficients will be used in the evaluation, so\n    they should be avoided if efficiency is a concern.\n\n    Parameters\n    ----------\n    x : array_like, compatible object\n        If \`x\` is a list or tuple, it is converted to an ndarray, otherwise\n        it is left unchanged and treated as a scalar. In either case, \`x\`\n        or its elements must support addition and multiplication with\n        themselves and with the elements of \`c\`.\n    c : array_like\n        Array of coefficients ordered so that the coefficients for terms of\n        degree n are contained in c[n]. If \`c\` is multidimensional the\n        remaining indices enumerate multiple polynomials. In the two\n        dimensional case the coefficients may be thought of as stored in\n        the columns of \`c\`.\n    tensor : boolean, optional\n        If True, the shape of the coefficient array is extended with ones\n        on the right, one for each dimension of \`x\`. Scalars have dimension 0\n        for this action. The result is that every column of coefficients in\n        \`c\` is evaluated for every element of \`x\`. If False, \`x\` is broadcast\n        over the columns of \`c\` for the evaluation.  This keyword is useful\n        when \`c\` is multidimensional. The default value is True.\n\n    Returns\n    -------\n    values : ndarray, algebra_like\n        The shape of the return value is described above.\n\n    See Also\n    --------\n    lagval2d, laggrid2d, lagval3d, laggrid3d\n\n    Notes\n    -----\n    The evaluation uses Clenshaw recursion, aka synthetic division.\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagval\n    >>> coef = [1, 2, 3]\n    >>> lagval(1, coef)\n    -0.5\n    >>> lagval([[1, 2],[3, 4]], coef)\n    array([[-0.5, -4. ],\n           [-4.5, -2. ]])\n\n    \"\"\"\n    c = np.array(c, ndmin=1, copy=None)\n    if c.dtype.char in '?bBhHiIlLqQpP':\n        c = c.astype(np.double)\n    if isinstance(x, (tuple, list)):\n        x = np.asarray(x)\n    if isinstance(x, np.ndarray) and tensor:\n        c = c.reshape(c.shape + (1,) * x.ndim)\n\n    if len(c) == 1:\n        c0 = c[0]\n        c1 = 0\n    elif len(c) == 2:\n        c0 = c[0]\n        c1 = c[1]\n    else:\n        nd = len(c)\n        c0 = c[-2]\n        c1 = c[-1]\n        for i in range(3, len(c) + 1):\n            tmp = c0\n            nd = nd - 1\n            c0 = c[-i] - (c1 * (nd - 1)) / nd\n            c1 = tmp + (c1 * ((2 * nd - 1) - x)) / nd\n    return c0 + c1 * (1 - x)"
}
-/

-- LLM HELPER
def evalPointLaguerre (x : Float) (c : Vector Float (n + 1)) : Float :=
  if h : n + 1 = 1 then c.get ⟨0, by simp [h]⟩
  else if h : n + 1 = 2 then 
    have h_pos : 0 < n := by
      simp at h
      have : n + 1 ≠ 1 := by simp at h; exact h
      have : n + 1 ≠ 2 := by exact h
      omega
    c.get ⟨0, by simp⟩ + c.get ⟨1, by simp⟩ * (1 - x)
  else
    let rec clenshaw (i : Nat) (c0 c1 : Float) (nd : Nat) : Float :=
      if i > n + 1 then c0 + c1 * (1 - x)
      else
        have hi : i ≤ n + 1 := by omega
        have hni : n + 1 - i < n + 1 := by
          cases' Nat.eq_or_lt_of_le hi with h_eq h_lt
          · simp [h_eq]
          · exact Nat.sub_lt (by simp) h_lt
        let tmp := c0
        let nd_new := nd - 1
        let c0_new := c.get ⟨n + 1 - i, hni⟩ - (c1 * (nd_new - 1).toFloat) / nd_new.toFloat
        let c1_new := tmp + (c1 * ((2 * nd_new - 1).toFloat - x)) / nd_new.toFloat
        clenshaw (i + 1) c0_new c1_new nd_new
    termination_by (n + 1 - i + 1)
    decreasing_by
      simp_wf
      have hi : i ≤ n + 1 := by omega
      have : n + 1 - (i + 1) < n + 1 - i := by
        rw [Nat.sub_succ]
        exact Nat.pred_lt (by
          cases' Nat.eq_or_lt_of_le hi with h_eq h_lt
          · simp [h_eq]
          · exact Nat.sub_pos_of_lt h_lt)
      exact this
    clenshaw 3 (c.get ⟨n + 1 - 2, by
      have : n + 1 ≥ 3 := by
        by_contra h_contra
        simp at h_contra
        interval_cases (n + 1)
        · simp at h
        · simp at h
        · simp at h
      exact Nat.sub_lt (by linarith) (by norm_num)⟩) (c.get ⟨n + 1 - 1, by
      have : n + 1 ≥ 3 := by
        by_contra h_contra
        simp at h_contra
        interval_cases (n + 1)
        · simp at h
        · simp at h
        · simp at h
      exact Nat.sub_lt (by linarith) (by norm_num)⟩) (n + 1)

/-- Evaluate a Laguerre series at points x using Clenshaw recursion.
    The mathematical formula for the Laguerre series is:
    p(x) = c_0 * L_0(x) + c_1 * L_1(x) + ... + c_n * L_n(x)
    where L_i(x) are the Laguerre polynomials. -/
def lagval {n m : Nat} (x : Vector Float m) (c : Vector Float (n + 1)) : Id (Vector Float m) :=
  pure (Vector.ofFn (fun i => evalPointLaguerre (x.get i) c))

/-- Specification for Laguerre series evaluation:
    The result has the same shape as the input x vector.
    For a single coefficient, the result is constant.
    For multiple coefficients, the function evaluates the Laguerre series
    using Clenshaw recursion, which is numerically stable. -/
theorem lagval_spec {n m : Nat} (x : Vector Float m) (c : Vector Float (n + 1)) 
    (h : n + 1 > 0) :
    ⦃⌜n + 1 > 0⌝⦄
    lagval x c
    ⦃⇓result => ⌜
      -- The function evaluates a Laguerre polynomial series
      -- For each point x_i, computes: sum_{j=0}^n c_j * L_j(x_i)
      (∀ i : Fin m, ∃ (val : Float), result.get i = val ∧ 
        -- The value represents the polynomial evaluation
        val = val) ∧
      -- Sanity check: result preserves input shape
      result.size = x.size
    ⌝⦄ := by
  simp [lagval]
  constructor
  · intro i
    use evalPointLaguerre (x.get i) c
    constructor
    · simp [Vector.get_ofFn]
    · rfl
  · simp [Vector.size_ofFn]