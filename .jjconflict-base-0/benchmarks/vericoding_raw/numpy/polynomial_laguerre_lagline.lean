import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.laguerre.lagline",
  "category": "Laguerre polynomials",
  "description": "Laguerre series whose graph is a straight line.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.laguerre.lagline.html",
  "doc": "Laguerre series whose graph is a straight line.\n\n    Parameters\n    ----------\n    off, scl : scalars\n        The specified line is given by \`\`off + scl*x\`\`.\n\n    Returns\n    -------\n    y : ndarray\n        This module's representation of the Laguerre series for\n        \`\`off + scl*x\`\`.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyline\n    numpy.polynomial.chebyshev.chebline\n    numpy.polynomial.legendre.legline\n    numpy.polynomial.hermite.hermline\n    numpy.polynomial.hermite_e.hermeline\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagline, lagval\n    >>> lagval(0,lagline(3, 2))\n    3.0\n    >>> lagval(1,lagline(3, 2))\n    5.0",
  "code": "def lagline(off, scl):\n    \"\"\"\n    Laguerre series whose graph is a straight line.\n\n    Parameters\n    ----------\n    off, scl : scalars\n        The specified line is given by \`\`off + scl*x\`\`.\n\n    Returns\n    -------\n    y : ndarray\n        This module's representation of the Laguerre series for\n        \`\`off + scl*x\`\`.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyline\n    numpy.polynomial.chebyshev.chebline\n    numpy.polynomial.legendre.legline\n    numpy.polynomial.hermite.hermline\n    numpy.polynomial.hermite_e.hermeline\n\n    Examples\n    --------\n    >>> from numpy.polynomial.laguerre import lagline, lagval\n    >>> lagval(0,lagline(3, 2))\n    3.0\n    >>> lagval(1,lagline(3, 2))\n    5.0\n\n    \"\"\"\n    if scl != 0:\n        return np.array([off + scl, -scl])\n    else:\n        return np.array([off])"
}
-/

/-- Laguerre series whose graph is a straight line off + scl*x -/
def lagline (off scl : Float) : Id (Vector Float 2) :=
  sorry

/-- Specification: lagline returns the Laguerre series representation of off + scl*x -/
theorem lagline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    lagline off scl
    ⦃⇓result => ⌜(scl = 0 → result.get 0 = off ∧ result.get 1 = 0) ∧
                 (scl ≠ 0 → result.get 0 = off + scl ∧ result.get 1 = -scl)⌝⦄ := by
  sorry