import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.polynomial.hermite_e.hermevander: Pseudo-Vandermonde matrix of given degree.

    Returns the pseudo-Vandermonde matrix of degree `deg` and sample points
    `x`. The pseudo-Vandermonde matrix is defined by

    .. math:: V[..., i] = He_i(x),

    where ``0 <= i <= deg``. The leading indices of `V` index the elements of
    `x` and the last index is the degree of the HermiteE polynomial.

    If `c` is a 1-D array of coefficients of length ``n + 1`` and `V` is the
    array ``V = hermevander(x, n)``, then ``np.dot(V, c)`` and
    ``hermeval(x, c)`` are the same up to roundoff. This equivalence is
    useful both for least squares fitting and for the evaluation of a large
    number of HermiteE series of the same degree and sample points.

    Parameters
    ----------
    x : array_like
        Array of points. The dtype is converted to float64 or complex128
        depending on whether any of the elements are complex. If `x` is
        scalar it is converted to a 1-D array.
    deg : int
        Degree of the resulting matrix.

    Returns
    -------
    vander : ndarray
        The pseudo-Vandermonde matrix. The shape of the returned matrix is
        ``x.shape + (deg + 1,)``, where The last index is the degree of the
        corresponding HermiteE polynomial.  The dtype will be the same as
        the converted `x`.
-/
def hermevander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry

/-- Specification: hermevander returns a pseudo-Vandermonde matrix where each row
    corresponds to a point in x, and each column corresponds to a HermiteE polynomial
    of degree 0 through deg evaluated at that point.

    The HermiteE polynomials (also called probabilist's Hermite polynomials) are
    defined by the recurrence relation:
    - He_0(x) = 1
    - He_1(x) = x  
    - He_n(x) = x * He_{n-1}(x) - (n-1) * He_{n-2}(x)

    Precondition: True (no special preconditions needed)
    Postcondition: 
    1. The matrix has shape (n, deg + 1)
    2. For each row i and column j, V[i][j] = He_j(x[i])
    3. First column is all ones (He_0(x) = 1)
    4. Second column equals x (He_1(x) = x) when deg > 0
    5. Subsequent columns follow the HermiteE recurrence relation
-/
theorem hermevander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    hermevander x deg
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- First column is all ones (He_0(x) = 1)
      (result.get i).get ⟨0, Nat.zero_lt_succ deg⟩ = 1 ∧
      
      -- Second column equals x when deg > 0 (He_1(x) = x)
      (deg > 0 → ∃ h : 1 < deg + 1, (result.get i).get ⟨1, h⟩ = x.get i) ∧
      
      -- For j ≥ 2: He_j(x) = x * He_{j-1}(x) - (j-1) * He_{j-2}(x)
      (∀ j : Fin (deg + 1), j.val ≥ 2 → 
        ∃ (h1 : j.val - 1 < deg + 1) (h2 : j.val - 2 < deg + 1),
        (result.get i).get j = 
          x.get i * (result.get i).get ⟨j.val - 1, h1⟩ - 
          (Float.ofNat (j.val - 1)) * (result.get i).get ⟨j.val - 2, h2⟩)⌝⦄ := by
  sorry