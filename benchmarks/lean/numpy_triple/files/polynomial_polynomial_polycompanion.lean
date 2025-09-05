/- 
{
  "name": "numpy.polynomial.polynomial.polycompanion",
  "category": "Standard polynomials",
  "description": "Return the companion matrix of c.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polynomial.polycompanion.html",
  "doc": "Return the companion matrix of c.\n\n    The companion matrix for power series cannot be made symmetric by\n    scaling the basis, so this function differs from those for the\n    orthogonal polynomials.\n\n    Parameters\n    ----------\n    c : array_like\n        1-D array of polynomial coefficients ordered from low to high\n        degree.\n\n    Returns\n    -------\n    mat : ndarray\n        Companion matrix of dimensions (deg, deg).\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polynomial as P\n    >>> c = (1, 2, 3)\n    >>> P.polycompanion(c)\n    array([[ 0.        , -0.33333333],\n           [ 1.        , -0.66666667]])",
}
-/

/-  Return the companion matrix of a polynomial.

    The companion matrix C for a polynomial p(x) = c[0] + c[1]*x + ... + c[n]*x^n
    is an (n×n) matrix where the characteristic polynomial is p(x).

    For a polynomial of degree n, the companion matrix has the form:
    - First (n-1) rows: [0, 0, ..., 0, 1, 0, ..., 0] (identity shifted)
    - Last row: [-c[0]/c[n], -c[1]/c[n], ..., -c[n-1]/c[n]]

    The companion matrix is used to find roots of the polynomial as eigenvalues. -/

/-  Specification: polycompanion constructs the companion matrix of a polynomial.

    The companion matrix satisfies the following properties:
    1. Dimension: Returns an (n+1)×(n+1) matrix for polynomial of degree n+1
    2. Structure: First n rows form shifted identity matrix pattern  
    3. Last row: Contains normalized negative coefficients [-c[0]/c[n+1], -c[1]/c[n+1], ..., -c[n]/c[n+1]]
    4. Leading coefficient: c[n+1] ≠ 0 (required for well-defined companion matrix)
    5. Eigenvalue property: The eigenvalues of the companion matrix are the roots of the polynomial

    Mathematical properties:
    - Characteristic polynomial: det(λI - C) = c[0] + c[1]*λ + ... + c[n+1]*λ^(n+1)
    - Rank: The matrix has full rank n+1 when c[n+1] ≠ 0
    - Structure: C[i,j] = 1 if j = i+1 and i < n, C[n,j] = -c[j]/c[n+1], 0 otherwise -/

import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polycompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry

theorem polycompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_leading : c.get ⟨n + 1, sorry⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, sorry⟩ ≠ 0⌝⦄
    polycompanion c
    ⦃⇓result => ⌜∀ i j : Fin (n + 1),
        (result.get i).get j = 
          if i.val + 1 = j.val ∧ i.val < n then 
            1
          else if i.val = n then 
            -(c.get ⟨j.val, sorry⟩) / (c.get ⟨n + 1, sorry⟩)
          else 
            0⌝⦄ := by
  sorry
