import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.hermite_e.hermegauss",
  "category": "HermiteE polynomials",
  "description": "Gauss-HermiteE quadrature.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermegauss.html",
  "doc": "Gauss-HermiteE quadrature.\n\n    Computes the sample points and weights for Gauss-HermiteE quadrature.\n    These sample points and weights will correctly integrate polynomials of\n    degree :math:\`2*deg - 1\` or less over the interval :math:\`[-\\\\inf, \\\\inf]\`\n    with the weight function :math:\`f(x) = \\\\exp(-x^2/2)\`.\n\n    Parameters\n    ----------\n    deg : int\n        Number of sample points and weights. It must be >= 1.\n\n    Returns\n    -------\n    x : ndarray\n        1-D ndarray containing the sample points.\n    y : ndarray\n        1-D ndarray containing the weights.\n\n    Notes\n    -----\n    The results have only been tested up to degree 100, higher degrees may\n    be problematic. The weights are determined by using the fact that\n\n    .. math:: w_k = c / (He'_n(x_k) * He_{n-1}(x_k))\n\n    where :math:\`c\` is a constant independent of :math:\`k\` and :math:\`x_k\`\n    is the k'th root of :math:\`He_n\`, and then scaling the results to get\n    the right value when integrating 1.",
  "code": "def hermegauss(deg):\n    \"\"\"\n    Gauss-HermiteE quadrature.\n\n    Computes the sample points and weights for Gauss-HermiteE quadrature.\n    These sample points and weights will correctly integrate polynomials of\n    degree :math:\`2*deg - 1\` or less over the interval :math:\`[-\\\\inf, \\\\inf]\`\n    with the weight function :math:\`f(x) = \\\\exp(-x^2/2)\`.\n\n    Parameters\n    ----------\n    deg : int\n        Number of sample points and weights. It must be >= 1.\n\n    Returns\n    -------\n    x : ndarray\n        1-D ndarray containing the sample points.\n    y : ndarray\n        1-D ndarray containing the weights.\n\n    Notes\n    -----\n    The results have only been tested up to degree 100, higher degrees may\n    be problematic. The weights are determined by using the fact that\n\n    .. math:: w_k = c / (He'_n(x_k) * He_{n-1}(x_k))\n\n    where :math:\`c\` is a constant independent of :math:\`k\` and :math:\`x_k\`\n    is the k'th root of :math:\`He_n\`, and then scaling the results to get\n    the right value when integrating 1.\n\n    \"\"\"\n    ideg = pu._as_int(deg, \"deg\")\n    if ideg <= 0:\n        raise ValueError(\"deg must be a positive integer\")\n\n    # first approximation of roots. We use the fact that the companion\n    # matrix is symmetric in this case in order to obtain better zeros.\n    c = np.array([0] * deg + [1])\n    m = hermecompanion(c)\n    x = la.eigvalsh(m)\n\n    # improve roots by one application of Newton\n    dy = _normed_hermite_e_n(x, ideg)\n    df = _normed_hermite_e_n(x, ideg - 1) * np.sqrt(ideg)\n    x -= dy / df\n\n    # compute the weights. We scale the factor to avoid possible numerical\n    # overflow.\n    fm = _normed_hermite_e_n(x, ideg - 1)\n    fm /= np.abs(fm).max()\n    w = 1 / (fm * fm)\n\n    # for Hermite_e we can also symmetrize\n    w = (w + w[::-1]) / 2\n    x = (x - x[::-1]) / 2\n\n    # scale w to get the right value\n    w *= np.sqrt(2 * np.pi) / w.sum()\n\n    return x, w"
}
-/

open Std.Do

/-- numpy.polynomial.hermite_e.hermegauss: Gauss-HermiteE quadrature.

    Computes the sample points and weights for Gauss-HermiteE quadrature.
    These sample points and weights will correctly integrate polynomials of
    degree 2*deg - 1 or less over the interval [-∞, ∞] with the weight
    function f(x) = exp(-x²/2).

    The function returns a pair (x, w) where x contains the sample points
    and w contains the corresponding weights.
-/
def hermegauss (deg : Nat) (h : deg > 0) : Id (Vector Float deg × Vector Float deg) :=
  sorry

/-- Specification: hermegauss returns quadrature points and weights for HermiteE polynomials.

    Precondition: deg > 0 (need at least one quadrature point)
    Postcondition: The returned points and weights satisfy the mathematical properties
    of Gauss-HermiteE quadrature including positivity, symmetry, and ordering.
-/
theorem hermegauss_spec (deg : Nat) (h : deg > 0) :
    ⦃⌜deg > 0⌝⦄
    hermegauss deg h
    ⦃⇓result => ⌜
      let (x, w) := result;
      -- Points are ordered (sorted in ascending order)
      (∀ i j : Fin deg, i < j → x.get i < x.get j) ∧
      -- Weights are positive 
      (∀ i : Fin deg, w.get i > 0) ∧
      -- Points are symmetric about origin
      (∀ i : Fin deg, ∃ j : Fin deg, x.get i = -(x.get j)) ∧
      -- Weights are symmetric (same symmetry as points)
      (∀ i : Fin deg, ∃ j : Fin deg, x.get i = -(x.get j) → w.get i = w.get j)
    ⌝⦄ := by
  sorry