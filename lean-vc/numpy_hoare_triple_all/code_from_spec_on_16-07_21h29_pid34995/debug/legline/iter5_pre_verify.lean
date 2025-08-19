import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legline",
  "category": "Legendre polynomials",
  "description": "Legendre series whose graph is a straight line.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legline.html",
  "doc": "Legendre series whose graph is a straight line.\n\n\n\n    Parameters\n    ----------\n    off, scl : scalars\n        The specified line is given by \`\`off + scl*x\`\`.\n\n    Returns\n    -------\n    y : ndarray\n        This module's representation of the Legendre series for\n        \`\`off + scl*x\`\`.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyline\n    numpy.polynomial.chebyshev.chebline\n    numpy.polynomial.laguerre.lagline\n    numpy.polynomial.hermite.hermline\n    numpy.polynomial.hermite_e.hermeline\n\n    Examples\n    --------\n    >>> import numpy.polynomial.legendre as L\n    >>> L.legline(3,2)\n    array([3, 2])\n    >>> L.legval(-3, L.legline(3,2)) # should be -3\n    -3.0",
  "code": "def legline(off, scl):\n    \"\"\"\n    Legendre series whose graph is a straight line.\n\n\n\n    Parameters\n    ----------\n    off, scl : scalars\n        The specified line is given by \`\`off + scl*x\`\`.\n\n    Returns\n    -------\n    y : ndarray\n        This module's representation of the Legendre series for\n        \`\`off + scl*x\`\`.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyline\n    numpy.polynomial.chebyshev.chebline\n    numpy.polynomial.laguerre.lagline\n    numpy.polynomial.hermite.hermline\n    numpy.polynomial.hermite_e.hermeline\n\n    Examples\n    --------\n    >>> import numpy.polynomial.legendre as L\n    >>> L.legline(3,2)\n    array([3, 2])\n    >>> L.legval(-3, L.legline(3,2)) # should be -3\n    -3.0\n\n    \"\"\"\n    if scl != 0:\n        return np.array([off, scl])\n    else:\n        return np.array([off])"
}
-/

/-- Creates a Legendre series representation of a straight line `off + scl*x` -/
def legline (off scl : Float) : Id (Vector Float 2) :=
  return ⟨#[off, scl], rfl⟩

/-- Specification: legline creates the correct Legendre series coefficients for a linear function -/
theorem legline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    legline off scl
    ⦃⇓result => 
      ⌜result.get 0 = off ∧ 
       result.get 1 = scl⌝⦄ := by
  unfold legline
  simp [pure, Vector.get]
  apply And.intro
  · simp [Array.get_mk]
  · simp [Array.get_mk]