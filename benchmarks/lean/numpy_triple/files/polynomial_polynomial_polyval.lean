/- 
{
  "name": "numpy.polynomial.polynomial.polyval",
  "category": "Standard polynomials",
  "description": "Evaluate a polynomial at points x.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polyval.html",
  "doc": "Evaluate a polynomial at points x.\n\n    If \`c\` is of length \`\`n + 1\`\`, this function returns the value\n\n    .. math:: p(x) = c_0 + c_1 * x + ... + c_n * x^n\n\n    The parameter \`x\` is converted to an array only if it is a tuple or a\n    list, otherwise it is treated as a scalar. In either case, either \`x\`\n    or its elements must support multiplication and addition both with\n    themselves and with the elements of \`c\`.\n\n    If \`c\` is a 1-D array, then \`\`p(x)\`\` will have the same shape as \`x\`.  If\n    \`c\` is multidimensional, then the shape of the result depends on the\n    value of \`tensor\`. If \`tensor\` is true the shape will be c.shape[1:] +\n    x.shape. If \`tensor\` is false the shape will be c.shape[1:]. Note that\n    scalars have shape (,).\n\n    Trailing zeros in the coefficients will be used in the evaluation, so\n    they should be avoided if efficiency is a concern.\n\n    Parameters\n    ----------\n    x : array_like, compatible object\n        If \`x\` is a list or tuple, it is converted to an ndarray, otherwise\n        it is left unchanged and treated as a scalar. In either case, \`x\`\n        or its elements must support addition and multiplication with\n        with themselves and with the elements of \`c\`.\n    c : array_like\n        Array of coefficients ordered so that the coefficients for terms of\n        degree n are contained in c[n]. If \`c\` is multidimensional the\n        remaining indices enumerate multiple polynomials. In the two\n        dimensional case the coefficients may be thought of as stored in\n        the columns of \`c\`.\n    tensor : boolean, optional\n        If True, the shape of the coefficient array is extended with ones\n        on the right, one for each dimension of \`x\`. Scalars have dimension 0\n        for this action. The result is that every column of coefficients in\n        \`c\` is evaluated for every element of \`x\`. If False, \`x\` is broadcast\n        over the columns of \`c\` for the evaluation.  This keyword is useful\n        when \`c\` is multidimensional. The default value is True.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The shape of the returned array is described above.\n\n    See Also\n    --------\n    polyval2d, polygrid2d, polyval3d, polygrid3d\n\n    Notes\n    -----\n    The evaluation uses Horner's method.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial.polynomial import polyval\n    >>> polyval(1, [1,2,3])\n    6.0\n    >>> a = np.arange(4).reshape(2,2)\n    >>> a\n    array([[0, 1],\n           [2, 3]])\n    >>> polyval(a, [1, 2, 3])\n    array([[ 1.,   6.],\n           [17.,  34.]])\n    >>> coef = np.arange(4).reshape(2, 2)  # multidimensional coefficients\n    >>> coef\n    array([[0, 1],\n           [2, 3]])\n    >>> polyval([1, 2], coef, tensor=True)\n    array([[2.,  4.],\n           [4.,  7.]])\n    >>> polyval([1, 2], coef, tensor=False)\n    array([2.,  7.])",
}
-/

/-  Evaluate a polynomial at points x using Horner's method.
    Given coefficients c = [c₀, c₁, ..., cₙ] and evaluation points x,
    computes p(x) = c₀ + c₁·x + c₂·x² + ... + cₙ·xⁿ for each x -/

/-  Specification: polyval evaluates a polynomial with coefficients c at points x.
    The result at each point xᵢ is the polynomial value p(xᵢ) = c₀ + c₁·xᵢ + c₂·xᵢ² + ... + cₙ·xᵢⁿ

    Mathematical properties:
    - For coefficient vector c = [c₀, c₁, ..., cₙ], evaluates polynomial p(x) = Σⱼ cⱼ·xʲ
    - Uses Horner's method for numerical stability: p(x) = c₀ + x·(c₁ + x·(c₂ + x·(...)))
    - Linear in coefficients: p(x, αc₁ + βc₂) = α·p(x, c₁) + β·p(x, c₂)
    - Polynomial evaluation at zero gives constant term: p(0) = c₀
    - For degree-0 polynomial [c₀], result is constant c₀ for all x -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polyval {m n : Nat} (x : Vector Float m) (c : Vector Float (n + 1)) : Id (Vector Float m) :=
  sorry

theorem polyval_spec {m n : Nat} (x : Vector Float m) (c : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    polyval x c
    ⦃⇓result => ⌜∀ i : Fin m, ∃ (poly_val : Float), result.get i = poly_val ∧
                  (n = 0 → poly_val = c.get ⟨0, Nat.zero_lt_succ _⟩) ∧
                  (∀ j : Fin (n + 1), c.get j = 0 → poly_val = 0)⌝⦄ := by
  sorry
