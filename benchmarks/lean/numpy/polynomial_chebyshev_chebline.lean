import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.chebyshev.chebline",
  "category": "Chebyshev polynomials",
  "description": "Chebyshev series whose graph is a straight line.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebline.html",
  "doc": "Chebyshev series whose graph is a straight line.\n\n    Parameters\n    ----------\n    off, scl : scalars\n        The specified line is given by ``off + scl*x``.\n\n    Returns\n    -------\n    y : ndarray\n        This module's representation of the Chebyshev series for\n        ``off + scl*x``.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyline\n    numpy.polynomial.legendre.legline\n    numpy.polynomial.laguerre.lagline\n    numpy.polynomial.hermite.hermline\n    numpy.polynomial.hermite_e.hermeline\n\n    Examples\n    --------\n    >>> import numpy.polynomial.chebyshev as C\n    >>> C.chebline(3,2)\n    array([3, 2])\n    >>> C.chebval(-3, C.chebline(3,2)) # should be -3\n    -3.0",
  "code": "def chebline(off, scl):\n    \"\"\"\n    Chebyshev series whose graph is a straight line.\n\n    Parameters\n    ----------\n    off, scl : scalars\n        The specified line is given by ``off + scl*x``.\n\n    Returns\n    -------\n    y : ndarray\n        This module's representation of the Chebyshev series for\n        ``off + scl*x``.\n\n    See Also\n    --------\n    numpy.polynomial.polynomial.polyline\n    numpy.polynomial.legendre.legline\n    numpy.polynomial.laguerre.lagline\n    numpy.polynomial.hermite.hermline\n    numpy.polynomial.hermite_e.hermeline\n\n    Examples\n    --------\n    >>> import numpy.polynomial.chebyshev as C\n    >>> C.chebline(3,2)\n    array([3, 2])\n    >>> C.chebval(-3, C.chebline(3,2)) # should be -3\n    -3.0\n\n    \"\"\"\n    if scl != 0:\n        return np.array([off, scl])\n    else:\n        return np.array([off])"
}
-/

open Std.Do

/-- Chebyshev series whose graph is a straight line.
    Returns coefficients for the Chebyshev series representing off + scl*x.
    For simplicity, we always return a 2-element vector where the second element
    might be zero when scl = 0. -/
def chebline (off scl : Float) : Id (Vector Float 2) :=
  sorry

/-- Specification: chebline returns correct Chebyshev coefficients for a linear function.
    The key mathematical property is that the Chebyshev series T₀(x) = 1 and T₁(x) = x,
    so the coefficients [off, scl] directly represent off*T₀(x) + scl*T₁(x) = off + scl*x.
    
    The result is always a 2-element vector [off, scl], even when scl = 0.
    This represents the Chebyshev series: off * T₀(x) + scl * T₁(x) = off + scl*x
    
    Mathematical Properties:
    1. The first coefficient equals the offset parameter
    2. The second coefficient equals the scale parameter
    3. When evaluated as a Chebyshev series, this produces the line off + scl*x
    4. This is the minimal degree Chebyshev representation of a linear function -/
theorem chebline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    chebline off scl
    ⦃⇓result => ⌜result.get ⟨0, by decide⟩ = off ∧ 
                 result.get ⟨1, by decide⟩ = scl⌝⦄ := by
  sorry