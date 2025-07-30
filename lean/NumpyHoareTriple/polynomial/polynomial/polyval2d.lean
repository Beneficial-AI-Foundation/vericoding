import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.polynomial.polyval2d",
  "category": "Standard polynomials",
  "description": "Evaluate a 2-D polynomial at points (x, y).",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polyval2d.html",
  "doc": "Evaluate a 2-D polynomial at points (x, y).\n\n    This function returns the value\n\n    .. math:: p(x,y) = \\\\sum_{i,j} c_{i,j} * x^i * y^j\n\n    The parameters \`x\` and \`y\` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars and they\n    must have the same shape after conversion. In either case, either \`x\`\n    and \`y\` or their elements must support multiplication and addition both\n    with themselves and with the elements of \`c\`.\n\n    If \`c\` has fewer than two dimensions, ones are implicitly appended to\n    its shape to make it 2-D. The shape of the result will be c.shape[2:] +\n    x.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points \`\`(x, y)\`\`,\n        where \`x\` and \`y\` must have the same shape. If \`x\` or \`y\` is a list\n        or tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and, if it isn't an ndarray, it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficient of the term\n        of multi-degree i,j is contained in \`\`c[i,j]\`\`. If \`c\` has\n        dimension greater than two the remaining indices enumerate multiple\n        sets of coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points formed with\n        pairs of corresponding values from \`x\` and \`y\`.\n\n    See Also\n    --------\n    polyval, polygrid2d, polyval3d, polygrid3d\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = ((1, 2, 3), (4, 5, 6))\n    >>> P.polyval2d(1, 1, c)\n    21.0",
  "code": "def polyval2d(x, y, c):\n    \"\"\"\n    Evaluate a 2-D polynomial at points (x, y).\n\n    This function returns the value\n\n    .. math:: p(x,y) = \\\\sum_{i,j} c_{i,j} * x^i * y^j\n\n    The parameters \`x\` and \`y\` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars and they\n    must have the same shape after conversion. In either case, either \`x\`\n    and \`y\` or their elements must support multiplication and addition both\n    with themselves and with the elements of \`c\`.\n\n    If \`c\` has fewer than two dimensions, ones are implicitly appended to\n    its shape to make it 2-D. The shape of the result will be c.shape[2:] +\n    x.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points \`\`(x, y)\`\`,\n        where \`x\` and \`y\` must have the same shape. If \`x\` or \`y\` is a list\n        or tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and, if it isn't an ndarray, it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficient of the term\n        of multi-degree i,j is contained in \`\`c[i,j]\`\`. If \`c\` has\n        dimension greater than two the remaining indices enumerate multiple\n        sets of coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points formed with\n        pairs of corresponding values from \`x\` and \`y\`.\n\n    See Also\n    --------\n    polyval, polygrid2d, polyval3d, polygrid3d\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = ((1, 2, 3), (4, 5, 6))\n    >>> P.polyval2d(1, 1, c)\n    21.0\n\n    \"\"\"\n    return pu._valnd(polyval, c, x, y)"
}
-/

open Std.Do

/-- Evaluate a 2D polynomial at points (x, y).
    Given a coefficient matrix c and evaluation points (x, y),
    computes p(x,y) = Σᵢⱼ cᵢⱼ·xⁱ·yʲ for each point pair -/
def polyval2d {m nx ny : Nat} (x y : Vector Float m) 
    (c : Vector (Vector Float (ny + 1)) (nx + 1)) : Id (Vector Float m) :=
  sorry

/-- Specification: polyval2d evaluates a 2D polynomial with coefficient matrix c at point pairs (x, y).
    The result at each point (xᵢ, yᵢ) is the polynomial value p(xᵢ, yᵢ) = Σᵢⱼ cᵢⱼ·xᵢⁱ·yᵢʲ
    
    Mathematical properties:
    - For coefficient matrix c[i][j], evaluates p(x,y) = Σᵢⱼ c[i][j]·xⁱ·yʲ
    - Reduces to 1D polyval when one variable is zero: p(x,0) uses first column c[*][0]
    - Bilinear in coefficients: p(x,y, αc₁ + βc₂) = α·p(x,y,c₁) + β·p(x,y,c₂)  
    - Constant term: p(0,0) = c[0][0]
    - Degree-0 in both variables gives constant: c = [[c₀₀]] → p(x,y) = c₀₀ for all (x,y) -/
theorem polyval2d_spec {m nx ny : Nat} (x y : Vector Float m) 
    (c : Vector (Vector Float (ny + 1)) (nx + 1)) :
    ⦃⌜True⌝⦄
    polyval2d x y c
    ⦃⇓result => ⌜∀ k : Fin m, ∃ (poly_val : Float), result.get k = poly_val ∧
                  -- Constant term property: when both degrees are 0
                  (nx = 0 ∧ ny = 0 → poly_val = (c.get ⟨0, Nat.zero_lt_succ _⟩).get ⟨0, Nat.zero_lt_succ _⟩) ∧
                  -- Zero coefficient property: if all coefficients are zero, result is zero
                  (∀ i : Fin (nx + 1), ∀ j : Fin (ny + 1), (c.get i).get j = 0 → poly_val = 0) ∧
                  -- Evaluation at origin gives constant term
                  (x.get k = 0 ∧ y.get k = 0 → poly_val = (c.get ⟨0, Nat.zero_lt_succ _⟩).get ⟨0, Nat.zero_lt_succ _⟩)⌝⦄ := by
  sorry