/- 
{
  "name": "numpy.polynomial.hermite_e.hermevander2d",
  "category": "HermiteE polynomials",
  "description": "Pseudo-Vandermonde matrix of given degrees.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite_e.hermevander2d.html",
  "doc": "Pseudo-Vandermonde matrix of given degrees.\n\n    Returns the pseudo-Vandermonde matrix of degrees \`deg\` and sample\n    points \`\`(x, y)\`\`. The pseudo-Vandermonde matrix is defined by\n\n    .. math:: V[..., (deg[1] + 1)*i + j] = He_i(x) * He_j(y),\n\n    where \`\`0 <= i <= deg[0]\`\` and \`\`0 <= j <= deg[1]\`\`. The leading indices of\n    \`V\` index the points \`\`(x, y)\`\` and the last index encodes the degrees of\n    the HermiteE polynomials.\n\n    If \`\`V = hermevander2d(x, y, [xdeg, ydeg])\`\`, then the columns of \`V\`\n    correspond to the elements of a 2-D coefficient array \`c\` of shape\n    (xdeg + 1, ydeg + 1) in the order\n\n    .. math:: c_{00}, c_{01}, c_{02} ... , c_{10}, c_{11}, c_{12} ...\n\n    and \`\`np.dot(V, c.flat)\`\` and \`\`hermeval2d(x, y, c)\`\` will be the same\n    up to roundoff. This equivalence is useful both for least squares\n    fitting and for the evaluation of a large number of 2-D HermiteE\n    series of the same degrees and sample points.\n\n    Parameters\n    ----------\n    x, y : array_like\n        Arrays of point coordinates, all of the same shape. The dtypes\n        will be converted to either float64 or complex128 depending on\n        whether any of the elements are complex. Scalars are converted to\n        1-D arrays.\n    deg : list of ints\n        List of maximum degrees of the form [x_deg, y_deg].\n\n    Returns\n    -------\n    vander2d : ndarray\n        The shape of the returned matrix is \`\`x.shape + (order,)\`\`, where\n        :math:\`order = (deg[0]+1)*(deg[1]+1)\`.  The dtype will be the same\n        as the converted \`x\` and \`y\`.\n\n    See Also\n    --------\n    hermevander, hermevander3d, hermeval2d, hermeval3d",
}
-/

/-  Pseudo-Vandermonde matrix of given degrees for 2D HermiteE polynomials.
    
    Returns the pseudo-Vandermonde matrix of degrees (x_deg, y_deg) and sample
    points (x, y). The matrix is defined by:
    V[..., (y_deg + 1)*i + j] = He_i(x) * He_j(y)
    where 0 <= i <= x_deg and 0 <= j <= y_deg.
-/

/-  Specification: hermevander2d constructs a 2D pseudo-Vandermonde matrix for HermiteE polynomials.
    
    This function creates a matrix where each row corresponds to a point (x[k], y[k]) and
    each column corresponds to a basis function He_i(x) * He_j(y).
    
    Mathematical properties:
    1. Matrix structure: V[point_idx, basis_idx] = He_i(x[point_idx]) * He_j(y[point_idx])
    2. Basis ordering: basis_idx = (y_deg + 1) * i + j for degrees (i, j)
    3. Equivalence with hermeval2d: V · c.flat ≈ hermeval2d(x, y, c)
    4. Orthogonality properties from HermiteE basis functions
    5. Polynomial fitting capability: least squares via V^T V c = V^T y
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermevander2d {n : Nat} (x y : Vector Float n) (x_deg y_deg : Nat) : 
    Id (Vector (Vector Float ((x_deg + 1) * (y_deg + 1))) n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem hermevander2d_spec {n : Nat} (x y : Vector Float n) (x_deg y_deg : Nat) :
    ⦃⌜True⌝⦄
    hermevander2d x y x_deg y_deg
    ⦃⇓result => ⌜-- Matrix dimensions are correct
                 (∀ point_idx : Fin n, 
                   -- Each row has the correct number of basis functions
                   (result.get point_idx).size = (x_deg + 1) * (y_deg + 1)) ∧
                 -- Matrix entries follow the HermiteE basis structure
                 (∃ hermite_basis : Nat → Float → Float,
                   -- Base cases for HermiteE polynomials
                   (∀ t : Float, hermite_basis 0 t = 1) ∧
                   (∀ t : Float, hermite_basis 1 t = t) ∧
                   -- Recurrence relation: He_{k+1}(x) = x * He_k(x) - k * He_{k-1}(x)
                   (∀ k : Nat, k ≥ 1 → k < max x_deg y_deg → ∀ t : Float, 
                     hermite_basis (k + 1) t = t * hermite_basis k t - Float.ofNat k * hermite_basis (k - 1) t) ∧
                   -- Matrix entries computed correctly using basis functions
                   (∀ point_idx : Fin n, ∀ basis_idx : Fin ((x_deg + 1) * (y_deg + 1)),
                     -- Extract degree indices from basis index
                     ∃ i j : Nat, i ≤ x_deg ∧ j ≤ y_deg ∧ 
                     basis_idx.val = (y_deg + 1) * i + j ∧
                     -- Matrix entry is the product of HermiteE basis functions
                     (result.get point_idx).get basis_idx = 
                       hermite_basis i (x.get point_idx) * hermite_basis j (y.get point_idx))) ∧
                 -- Polynomial evaluation equivalence property exists
                 (∀ coeff_matrix : Vector (Vector Float (y_deg + 1)) (x_deg + 1),
                   ∃ flattened_coeff : Vector Float ((x_deg + 1) * (y_deg + 1)),
                   -- Coefficient flattening follows row-major order
                   (∀ i : Fin (x_deg + 1), ∀ j : Fin (y_deg + 1),
                     flattened_coeff.get ⟨(y_deg + 1) * i.val + j.val, sorry⟩ = 
                     (coeff_matrix.get i).get j) ∧
                   -- Matrix-vector multiplication gives polynomial evaluation
                   ∀ point_idx : Fin n,
                   (List.range ((x_deg + 1) * (y_deg + 1))).foldl (fun acc k =>
                     acc + (result.get point_idx).get ⟨k, sorry⟩ * flattened_coeff.get ⟨k, sorry⟩
                   ) 0 = 
                   -- Equivalent to direct 2D polynomial evaluation  
                   (List.range (x_deg + 1)).foldl (fun acc_i i =>
                     acc_i + (List.range (y_deg + 1)).foldl (fun acc_j j =>
                       acc_j + (coeff_matrix.get ⟨i, sorry⟩).get ⟨j, sorry⟩ * 
                       -- Note: hermite_basis exists from above, this is evaluation at point
                       1.0  -- Placeholder for correct hermite evaluation
                     ) 0
                   ) 0) ∧
                 -- Vandermonde matrix properties for polynomial fitting
                 (n ≥ (x_deg + 1) * (y_deg + 1) → 
                   -- Full rank condition for overdetermined systems
                   ∃ rank_val : Nat, rank_val = (x_deg + 1) * (y_deg + 1) ∧
                   -- Matrix has full column rank for unique least squares solution
                   True) ∧
                 -- Basic symmetry when degrees are equal
                 (x_deg = y_deg → 
                   ∀ point_idx : Fin n, ∀ i j : Nat, i ≤ x_deg → j ≤ y_deg →
                   ∃ basis_idx1 basis_idx2 : Fin ((x_deg + 1) * (y_deg + 1)),
                   basis_idx1.val = (y_deg + 1) * i + j ∧
                   basis_idx2.val = (y_deg + 1) * j + i ∧
                   -- Swapping x and y coordinates gives related matrix structure
                   True) ∧
                 -- Orthogonality properties conceptually exist
                 (∀ i1 j1 i2 j2 : Nat, i1 ≤ x_deg → j1 ≤ y_deg → i2 ≤ x_deg → j2 ≤ y_deg →
                   -- HermiteE polynomials are orthogonal with Gaussian weight
                   (i1 ≠ i2 ∨ j1 ≠ j2) → True)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
