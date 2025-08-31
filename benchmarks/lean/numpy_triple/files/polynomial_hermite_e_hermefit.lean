/- 
{
  "name": "numpy.polynomial.hermite_e.hermefit",
  "category": "HermiteE polynomials",
  "description": "Least squares fit of Hermite series to data.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermefit.html",
  "doc": "Least squares fit of Hermite series to data.\n\n    Return the coefficients of a HermiteE series of degree `deg` that is\n    the least squares fit to the data values `y` given at points `x`. If\n    `y` is 1-D the returned coefficients will also be 1-D. If `y` is 2-D\n    multiple fits are done, one for each column of `y`, and the resulting\n    coefficients are stored in the corresponding columns of a 2-D return.\n    The fitted polynomial(s) are in the form\n\n    .. math::  p(x) = c_0 + c_1 * He_1(x) + ... + c_n * He_n(x),\n\n    where `n` is `deg`.\n\n    Parameters\n    ----------\n    x : array_like, shape (M,)\n        x-coordinates of the M sample points `(x[i], y[i])`.\n    y : array_like, shape (M,) or (M, K)\n        y-coordinates of the sample points. Several data sets of sample\n        points sharing the same x-coordinates can be fitted at once by\n        passing in a 2D-array that contains one dataset per column.\n    deg : int or 1-D array_like\n        Degree(s) of the fitting polynomials. If `deg` is a single integer\n        all terms up to and including the `deg`'th term are included in the\n        fit. For NumPy versions >= 1.11.0 a list of integers specifying the\n        degrees of the terms to include may be used instead.\n    rcond : float, optional\n        Relative condition number of the fit. Singular values smaller than\n        this relative to the largest singular value will be ignored. The\n        default value is len(x)*eps, where eps is the relative precision of\n        the float type, about 2e-16 in most cases.\n    full : bool, optional\n        Switch determining nature of return value. When it is False (the\n        default) just the coefficients are returned, when True diagnostic\n        information from the singular value decomposition is also returned.\n    w : array_like, shape (`M`,), optional\n        Weights. If not None, the weight `w[i]` applies to the unsquared\n        residual `y[i] - y_hat[i]` at `x[i]`. Ideally the weights are\n        chosen so that the errors of the products `w[i]*y[i]` all have the\n        same variance.  When using inverse-variance weighting, use\n        `w[i] = 1/sigma(y[i])`.  The default value is None.\n\n    Returns\n    -------\n    coef : ndarray, shape (M,) or (M, K)\n        Hermite coefficients ordered from low to high. If `y` was 2-D,\n        the coefficients for the data in column k  of `y` are in column\n        `k`.\n\n    [residuals, rank, singular_values, rcond] : list\n        These values are only returned if `full == True`\n\n        - residuals -- sum of squared residuals of the least squares fit\n        - rank -- the numerical rank of the scaled Vandermonde matrix\n        - singular_values -- singular values of the scaled Vandermonde matrix\n        - rcond -- value of `rcond`.\n\n        For more details, see `numpy.linalg.lstsq`.\n\n    Warns\n    -----\n    RankWarning\n        The rank of the coefficient matrix in the least-squares fit is\n        deficient. The warning is only raised if `full = False`.  The\n        warnings can be turned off by\n\n        >>> import warnings\n        >>> warnings.simplefilter('ignore', np.exceptions.RankWarning)\n\n    See Also\n    --------\n    numpy.polynomial.chebyshev.chebfit\n    numpy.polynomial.legendre.legfit\n    numpy.polynomial.polynomial.polyfit\n    numpy.polynomial.hermite.hermfit\n    numpy.polynomial.laguerre.lagfit\n    hermeval : Evaluates a Hermite series.\n    hermevander : pseudo Vandermonde matrix of Hermite series.\n    hermeweight : HermiteE weight function.\n    numpy.linalg.lstsq : Computes a least-squares fit from the matrix.\n    scipy.interpolate.UnivariateSpline : Computes spline fits.\n\n    Notes\n    -----\n    The solution is the coefficients of the HermiteE series `p` that\n    minimizes the sum of the weighted squared errors\n\n    .. math:: E = \\\\sum_j w_j^2 * |y_j - p(x_j)|^2,\n\n    where the :math:`w_j` are the weights. This problem is solved by\n    setting up the (typically) overdetermined matrix equation\n\n    .. math:: V(x) * c = w * y,\n\n    where `V` is the pseudo Vandermonde matrix of `x`, the elements of `c`\n    are the coefficients to be solved for, and the elements of `y` are the\n    observed values.  This equation is then solved using the singular value\n    decomposition of `V`.\n\n    If some of the singular values of `V` are so small that they are\n    neglected, then a `~exceptions.RankWarning` will be issued. This means that\n    the coefficient values may be poorly determined. Using a lower order fit\n    will usually get rid of the warning.  The `rcond` parameter can also be\n    set to a value smaller than its default, but the resulting fit may be\n    spurious and have large contributions from roundoff error.\n\n    Fits using HermiteE series are probably most useful when the data can\n    be approximated by `sqrt(w(x)) * p(x)`, where `w(x)` is the HermiteE\n    weight. In that case the weight `sqrt(w(x[i]))` should be used\n    together with data values `y[i]/sqrt(w(x[i]))`. The weight function is\n    available as `hermeweight`.\n\n    References\n    ----------\n    .. [1] Wikipedia, \"Curve fitting\",\n           https://en.wikipedia.org/wiki/Curve_fitting\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> from numpy.polynomial.hermite_e import hermefit, hermeval\n    >>> x = np.linspace(-10, 10)\n    >>> rng = np.random.default_rng()\n    >>> err = rng.normal(scale=1./10, size=len(x))\n    >>> y = hermeval(x, [1, 2, 3]) + err\n    >>> hermefit(x, y, 2)\n    array([1.02284196, 2.00032805, 2.99978457]) # may vary",
}
-/

/-  Least squares fit of Hermite series to data.
    Returns the coefficients of a HermiteE series of degree `deg` that is
    the least squares fit to the data values `y` given at points `x`. -/

/-  Specification: hermefit performs least squares fitting of Hermite series to data.
    The function returns coefficients that minimize the sum of squared residuals
    when the Hermite series is evaluated at the given points. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Helper function for Hermite_e polynomial evaluation (probabilist's Hermite polynomials)
    He_n(x) = (-1)^n * exp(x^2/2) * d^n/dx^n * exp(-x^2/2) -/
def hermiteE : Nat → Float → Float
| 0, _ => 1
| 1, x => x  
| n + 2, x => 
    let coeff := Float.ofNat (n + 1)
    x * hermiteE (n + 1) x - coeff * hermiteE n x

-- <vc-helpers>
-- </vc-helpers>

def hermefit {m : Nat} (x : Vector Float m) (y : Vector Float m) (deg : Nat) 
    (h_size : deg + 1 ≤ m) (h_nonempty : m > 0) : Id (Vector Float (deg + 1)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem hermefit_spec {m : Nat} (x : Vector Float m) (y : Vector Float m) (deg : Nat)
    (h_size : deg + 1 ≤ m) (h_nonempty : m > 0) :
    ⦃⌜deg + 1 ≤ m ∧ m > 0⌝⦄
    hermefit x y deg h_size h_nonempty
    ⦃⇓coef => ⌜
      -- Sanity check: coefficients are finite
      (∀ i : Fin (deg + 1), 
        let ci := coef.get i
        ¬ci.isNaN ∧ ¬ci.isInf) ∧
      -- Basic property: the result has the correct size
      coef.size = deg + 1 ∧
      -- Least squares property: the coefficients minimize the sum of squared residuals
      -- For any other coefficient vector c of the same degree,
      -- the sum of squared residuals using coef is ≤ that using c
      (∀ c : Vector Float (deg + 1), 
        let residual_coef := (List.finRange m).map (fun i => 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (coef.get j) * (hermiteE j.val xi)) 0
          (yi - pred) ^ 2)
        let residual_c := (List.finRange m).map (fun i => 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (c.get j) * (hermiteE j.val xi)) 0
          (yi - pred) ^ 2)
        residual_coef.sum ≤ residual_c.sum) ∧
      -- Exact interpolation property: when we have exactly deg+1 points,
      -- the polynomial passes through all points exactly
      (deg + 1 = m → 
        ∀ i : Fin m, 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (coef.get j) * (hermiteE j.val xi)) 0
          Float.abs (yi - pred) < 1e-10) ∧
      -- Orthogonality condition: the residuals are orthogonal to the basis functions
      -- This is a fundamental property of least squares solutions
      (∀ k : Fin (deg + 1), 
        let residuals := (List.finRange m).map (fun i => 
          let xi := x.get i
          let yi := y.get i
          let pred := (List.finRange (deg + 1)).foldl (fun acc j => 
            acc + (coef.get j) * (hermiteE j.val xi)) 0
          yi - pred)
        let basis_vals := (List.finRange m).map (fun i => 
          hermiteE k.val (x.get i))
        Float.abs ((residuals.zip basis_vals).map (fun p => p.1 * p.2)).sum < 1e-10)
    ⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
