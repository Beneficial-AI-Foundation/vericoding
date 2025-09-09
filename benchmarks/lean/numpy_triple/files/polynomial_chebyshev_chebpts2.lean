/- 
{
  "name": "numpy.polynomial.chebyshev.chebpts2",
  "category": "Chebyshev polynomials",
  "description": "Chebyshev points of the second kind.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.chebpts2.html",
  "doc": "Chebyshev points of the second kind.\n\n    The Chebyshev points of the second kind are the points ``cos(x)``,\n    where ``x = [pi*k/(npts - 1) for k in range(npts)]`` sorted in ascending\n    order.\n\n    Parameters\n    ----------\n    npts : int\n        Number of sample points desired.\n\n    Returns\n    -------\n    pts : ndarray\n        The Chebyshev points of the second kind.",
}
-/

/-  Chebyshev points of the second kind.

    Generates n Chebyshev points of the second kind, which are the values
    cos(π*k/(n-1)) for k from 0 to n-1, sorted in ascending order.
    These points are the extrema and endpoints of the Chebyshev polynomial T_{n-1}. -/

/-  Specification: chebpts2 generates Chebyshev points of the second kind

    The function returns n points where:
    1. Each point is cos(π*k/(n-1)) for k from n-1 down to 0
    2. The points are sorted in ascending order
    3. The first point is -1 and the last point is 1
    4. The points are symmetric around 0 for the transformation x ↦ -x -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def chebpts2 (n : Nat) (h : n ≥ 2) : Id (Vector Float n) :=
  sorry

theorem chebpts2_spec (n : Nat) (h : n ≥ 2) :
    ⦃⌜n ≥ 2⌝⦄
    chebpts2 n h
    ⦃⇓pts => ⌜-- Points are sorted in ascending order
              (∀ i j : Fin n, i < j → pts.get i ≤ pts.get j) ∧
              -- First point is -1 (cos(π))
              pts.get ⟨0, Nat.zero_lt_of_lt h⟩ = -1 ∧
              -- Last point is 1 (cos(0))
              pts.get ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.zero_lt_one⟩ = 1 ∧
              -- All points are in the range [-1, 1]
              (∀ i : Fin n, -1 ≤ pts.get i ∧ pts.get i ≤ 1) ∧
              -- Points are distinct (strict monotonicity)
              (∀ i j : Fin n, i < j → pts.get i < pts.get j) ∧
              -- For n = 2, we have exactly {-1, 1}
              (n = 2 → pts.get ⟨0, sorry⟩ = -1 ∧ pts.get ⟨1, sorry⟩ = 1) ∧
              -- For n = 3, the middle point is 0
              (n = 3 → pts.get ⟨1, sorry⟩ = 0)⌝⦄ := by
  sorry
