-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legroots",
  "category": "Legendre polynomials",
  "description": "Compute the roots of a Legendre series.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legroots.html",
  "doc": "Compute the roots of a Legendre series.\n\n    Return the roots (a.k.a. \"zeros\") of the polynomial\n\n    .. math:: p(x) = \\\\sum_i c[i] * L_i(x).\n\n    Parameters\n    ----------\n    c : 1-D array_like\n        1-D array of coefficients.\n\n    Returns\n    -------\n    out : ndarray\n        Array of the roots of the series. If all the roots are real,\n        then \`out\` is also real, otherwise it is complex.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyroots\n    numpy.polynomial.chebyshev.chebroots\n    numpy.polynomial.laguerre.lagroots\n    numpy.polynomial.hermite.hermroots\n    numpy.polynomial.hermite_e.hermeroots\n\n    Notes\n    -----\n    The root estimates are obtained as the eigenvalues of the companion\n    matrix, Roots far from the origin of the complex plane may have large\n    errors due to the numerical instability of the series for such values.\n    Roots with multiplicity greater than 1 will also show larger errors as\n    the value of the series near such points is relatively insensitive to\n    errors in the roots. Isolated roots near the origin can be improved by\n    a few iterations of Newton's method.\n\n    The Legendre series basis polynomials aren't powers of \`\`x\`\` so the\n    results of this function may seem unintuitive.\n\n    Examples\n    --------\n    >>> import numpy.polynomial.legendre as leg\n    >>> leg.legroots((1, 2, 3, 4)) # 4L_3 + 3L_2 + 2L_1 + 1L_0, all real roots\n    array([-0.85099543, -0.11407192,  0.51506735]) # may vary",
  "code": "def legroots(c):\n    \"\"\"\n    Compute the roots of a Legendre series.\n\n    Return the roots (a.k.a. \"zeros\") of the polynomial\n\n    .. math:: p(x) = \\\\sum_i c[i] * L_i(x).\n\n    Parameters\n    ----------\n    c : 1-D array_like\n        1-D array of coefficients.\n\n    Returns\n    -------\n    out : ndarray\n        Array of the roots of the series. If all the roots are real,\n        then \`out\` is also real, otherwise it is complex.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyroots\n    numpy.polynomial.chebyshev.chebroots\n    numpy.polynomial.laguerre.lagroots\n    numpy.polynomial.hermite.hermroots\n    numpy.polynomial.hermite_e.hermeroots\n\n    Notes\n    -----\n    The root estimates are obtained as the eigenvalues of the companion\n    matrix, Roots far from the origin of the complex plane may have large\n    errors due to the numerical instability of the series for such values.\n    Roots with multiplicity greater than 1 will also show larger errors as\n    the value of the series near such points is relatively insensitive to\n    errors in the roots. Isolated roots near the origin can be improved by\n    a few iterations of Newton's method.\n\n    The Legendre series basis polynomials aren't powers of \`\`x\`\` so the\n    results of this function may seem unintuitive.\n\n    Examples\n    --------\n    >>> import numpy.polynomial.legendre as leg\n    >>> leg.legroots((1, 2, 3, 4)) # 4L_3 + 3L_2 + 2L_1 + 1L_0, all real roots\n    array([-0.85099543, -0.11407192,  0.51506735]) # may vary\n\n    \"\"\"\n    # c is a trimmed copy\n    [c] = pu.as_series([c])\n    if len(c) < 2:\n        return np.array([], dtype=c.dtype)\n    if len(c) == 2:\n        return np.array([-c[0] / c[1]])\n\n    # rotated companion matrix reduces error\n    m = legcompanion(c)[::-1, ::-1]\n    r = la.eigvals(m)\n    r.sort()\n    return r"
}
-/

/-- Helper function to evaluate a Legendre polynomial at a given point -/
def legendrePolynomialValue {n : Nat} (c : Vector Float n) (x : Float) : Float :=
  sorry

/-- Compute the roots of a Legendre series.
    Return the roots (a.k.a. "zeros") of the polynomial p(x) = ∑ᵢ c[i] * L_i(x).
    The coefficients are ordered from low to high. -/
def legroots {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float n) :=
  sorry

/-- Specification: legroots computes the roots of a Legendre polynomial series -/
theorem legroots_spec {n : Nat} (c : Vector Float (n + 1)) 
    (h_leading : c.get ⟨n, Nat.lt_succ_self n⟩ ≠ 0) :
    ⦃⌜c.get ⟨n, Nat.lt_succ_self n⟩ ≠ 0⌝⦄
    legroots c
    ⦃⇓roots => ⌜(∀ i : Fin n, 
                  legendrePolynomialValue c (roots.get i) = 0) ∧
                (∀ x : Float, legendrePolynomialValue c x = 0 → 
                  ∃ j : Fin n, roots.get j = x) ∧
                (∀ i j : Fin n, i ≠ j → roots.get i ≠ roots.get j)⌝⦄ := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>