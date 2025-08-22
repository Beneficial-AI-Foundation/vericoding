import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.polyutils.getdomain",
  "category": "Polynomial utilities",
  "description": "Return a domain suitable for given abscissae.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polyutils.getdomain.html",
  "doc": "Return a domain suitable for given abscissae.\n\n    Find a domain suitable for a polynomial or Chebyshev series\n    defined at the values supplied.\n\n    Parameters\n    ----------\n    x : array_like\n        1-d array of abscissae whose domain will be determined.\n\n    Returns\n    -------\n    domain : ndarray\n        1-d array containing two values.  If the inputs are complex, then\n        the two returned points are the lower left and upper right corners\n        of the smallest rectangle (aligned with the axes) in the complex\n        plane containing the points \`x\`. If the inputs are real, then the\n        two points are the ends of the smallest interval containing the\n        points \`x\`.\n\n    See Also\n    --------\n    mapparms, mapdomain\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial import polyutils as pu\n    >>> points = np.arange(4)**2 - 5; points\n    array([-5, -4, -1,  4])\n    >>> pu.getdomain(points)\n    array([-5.,  4.])\n    >>> c = np.exp(complex(0,1)*np.pi*np.arange(12)/6) # unit circle\n    >>> pu.getdomain(c)\n    array([-1.-1.j,  1.+1.j])",
  "code": "def getdomain(x):\n    \"\"\"\n    Return a domain suitable for given abscissae.\n\n    Find a domain suitable for a polynomial or Chebyshev series\n    defined at the values supplied.\n\n    Parameters\n    ----------\n    x : array_like\n        1-d array of abscissae whose domain will be determined.\n\n    Returns\n    -------\n    domain : ndarray\n        1-d array containing two values.  If the inputs are complex, then\n        the two returned points are the lower left and upper right corners\n        of the smallest rectangle (aligned with the axes) in the complex\n        plane containing the points \`x\`. If the inputs are real, then the\n        two points are the ends of the smallest interval containing the\n        points \`x\`.\n\n    See Also\n    --------\n    mapparms, mapdomain\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial import polyutils as pu\n    >>> points = np.arange(4)**2 - 5; points\n    array([-5, -4, -1,  4])\n    >>> pu.getdomain(points)\n    array([-5.,  4.])\n    >>> c = np.exp(complex(0,1)*np.pi*np.arange(12)/6) # unit circle\n    >>> pu.getdomain(c)\n    array([-1.-1.j,  1.+1.j])\n\n    \"\"\"\n    [x] = as_series([x], trim=False)\n    if x.dtype.char in np.typecodes['Complex']:\n        rmin, rmax = x.real.min(), x.real.max()\n        imin, imax = x.imag.min(), x.imag.max()\n        return np.array((complex(rmin, imin), complex(rmax, imax)))\n    else:\n        return np.array((x.min(), x.max()))"
}
-/

open Std.Do

/-- Return a domain suitable for given abscissae (real numbers).
    For real inputs, returns the minimum and maximum values as a 2-element vector.
    This represents the smallest interval containing all points in the input vector. -/
def getdomain {n : Nat} (x : Vector Float (n + 1)) : Id (Vector Float 2) :=
  sorry

/-- Specification: getdomain returns the smallest interval containing all input points -/
theorem getdomain_spec {n : Nat} (x : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    getdomain x
    ⦃⇓result => ⌜
      -- The minimum is less than or equal to the maximum
      result[0] ≤ result[1] ∧
      -- Every element in x is within the domain
      (∀ i : Fin (n + 1), result[0] ≤ x[i] ∧ x[i] ≤ result[1]) ∧
      -- The domain bounds are achieved by some elements in x
      (∃ i : Fin (n + 1), x[i] = result[0]) ∧
      (∃ j : Fin (n + 1), x[j] = result[1])
    ⌝⦄ := by
  sorry