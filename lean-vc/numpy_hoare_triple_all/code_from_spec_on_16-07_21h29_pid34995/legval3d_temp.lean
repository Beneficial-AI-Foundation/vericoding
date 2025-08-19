import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.polynomial.legendre.legval3d",
  "category": "Legendre polynomials",
  "description": "Evaluate a 3-D Legendre series at points (x, y, z).",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.legendre.legval3d.html",
  "doc": "Evaluate a 3-D Legendre series at points (x, y, z).\n\n    This function returns the values:\n\n    .. math:: p(x,y,z) = \\\\sum_{i,j,k} c_{i,j,k} * L_i(x) * L_j(y) * L_k(z)\n\n    The parameters \`x\`, \`y\`, and \`z\` are converted to arrays only if\n    they are tuples or a lists, otherwise they are treated as a scalars and\n    they must have the same shape after conversion. In either case, either\n    \`x\`, \`y\`, and \`z\` or their elements must support multiplication and\n    addition both with themselves and with the elements of \`c\`.\n\n    If \`c\` has fewer than 3 dimensions, ones are implicitly appended to its\n    shape to make it 3-D. The shape of the result will be c.shape[3:] +\n    x.shape.\n\n    Parameters\n    ----------\n    x, y, z : array_like, compatible object\n        The three dimensional series is evaluated at the points\n        \`\`(x, y, z)\`\`, where \`x\`, \`y\`, and \`z\` must have the same shape.  If\n        any of \`x\`, \`y\`, or \`z\` is a list or tuple, it is first converted\n        to an ndarray, otherwise it is left unchanged and if it isn't an\n        ndarray it is  treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficient of the term of\n        multi-degree i,j,k is contained in \`\`c[i,j,k]\`\`. If \`c\` has dimension\n        greater than 3 the remaining indices enumerate multiple sets of\n        coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the multidimensional polynomial on points formed with\n        triples of corresponding values from \`x\`, \`y\`, and \`z\`.\n\n    See Also\n    --------\n    legval, legval2d, leggrid2d, leggrid3d\n    \"\"\"\n    return pu._valnd(legval, c, x, y, z)"
}
-/

/-- Legendre polynomial L_n(x) evaluated using the recursive definition.
    L_0(x) = 1, L_1(x) = x, and (n+1)L_{n+1}(x) = (2n+1)x L_n(x) - n L_{n-1}(x) -/
def legendrePolynomial (n : Nat) (x : Float) : Float := 
  match n with
  | 0 => 1.0
  | 1 => x
  | n + 2 => 
    let prev2 := legendrePolynomial n x
    let prev1 := legendrePolynomial (n + 1) x
    let n_float := n.toFloat
    ((2 * n_float + 3) * x * prev1 - (n_float + 1) * prev2) / (n_float + 2)

-- LLM HELPER
def sumTriple {nx ny nz m : Nat} (x y z : Vector Float m) 
    (c : Vector (Vector (Vector Float (nz + 1)) (ny + 1)) (nx + 1)) 
    (k : Fin m) : Float :=
  let rec sumI (i : Nat) (acc : Float) : Float :=
    if i > nx then acc
    else
      let rec sumJ (j : Nat) (acc_j : Float) : Float :=
        if j > ny then acc_j
        else
          let rec sumK (k_idx : Nat) (acc_k : Float) : Float :=
            if k_idx > nz then acc_k
            else
              have i_bound : i < nx + 1 := Nat.lt_succ_iff.mpr (Nat.le_of_not_gt (fun h => by contradiction))
              have j_bound : j < ny + 1 := Nat.lt_succ_iff.mpr (Nat.le_of_not_gt (fun h => by contradiction))
              have k_bound : k_idx < nz + 1 := Nat.lt_succ_iff.mpr (Nat.le_of_not_gt (fun h => by contradiction))
              let coeff := ((c.get ⟨i, i_bound⟩).get ⟨j, j_bound⟩).get ⟨k_idx, k_bound⟩
              let term := coeff * legendrePolynomial i (x.get k) * legendrePolynomial j (y.get k) * legendrePolynomial k_idx (z.get k)
              sumK (k_idx + 1) (acc_k + term)
            termination_by nz + 1 - k_idx
          sumJ (j + 1) (acc_j + sumK 0 0.0)
        termination_by ny + 1 - j
      sumI (i + 1) (acc + sumJ 0 0.0)
    termination_by nx + 1 - i
  sumI 0 0.0

/-- Evaluate a 3-D Legendre series at points (x, y, z).
    For coefficients c[i,j,k], computes p(x,y,z) = ∑_{i,j,k} c[i,j,k] * L_i(x) * L_j(y) * L_k(z) -/
def legval3d {nx ny nz m : Nat} (x y z : Vector Float m) 
    (c : Vector (Vector (Vector Float (nz + 1)) (ny + 1)) (nx + 1)) : Id (Vector Float m) :=
  Vector.ofFn (fun k => sumTriple x y z c k)

-- LLM HELPER
lemma legendre_0 (x : Float) : legendrePolynomial 0 x = 1 := by
  simp [legendrePolynomial]

-- LLM HELPER
lemma legendre_1 (x : Float) : legendrePolynomial 1 x = x := by
  simp [legendrePolynomial]

-- LLM HELPER
lemma base_case_helper {nx ny nz m : Nat} (x y z : Vector Float m) 
    (c : Vector (Vector (Vector Float (nz + 1)) (ny + 1)) (nx + 1)) 
    (k : Fin m) (h1 : nx = 0) (h2 : ny = 0) (h3 : nz = 0) :
    sumTriple x y z c k = 
    ((c.get ⟨0, Nat.zero_lt_succ nx⟩).get ⟨0, Nat.zero_lt_succ ny⟩).get ⟨0, Nat.zero_lt_succ nz⟩ * 
    legendrePolynomial 0 (x.get k) * legendrePolynomial 0 (y.get k) * legendrePolynomial 0 (z.get k) := by
  simp [sumTriple, h1, h2, h3]
  ring

/-- Specification: legval3d evaluates a 3-D Legendre series using tensor product of 1D Legendre polynomials.
    The result at each point is the triple sum over Legendre polynomials in x, y, and z directions. -/
theorem legval3d_spec {nx ny nz m : Nat} (x y z : Vector Float m) 
    (c : Vector (Vector (Vector Float (nz + 1)) (ny + 1)) (nx + 1)) :
    ⦃⌜True⌝⦄
    legval3d x y z c
    ⦃⇓result => ⌜∀ k : Fin m, 
      -- Base case: constant term (degree 0,0,0)
      (nx = 0 ∧ ny = 0 ∧ nz = 0 → result.get k = 
        ((c.get ⟨0, Nat.zero_lt_succ nx⟩).get ⟨0, Nat.zero_lt_succ ny⟩).get ⟨0, Nat.zero_lt_succ nz⟩ * 
        legendrePolynomial 0 (x.get k) * legendrePolynomial 0 (y.get k) * legendrePolynomial 0 (z.get k)) ∧
      -- Mathematical properties of Legendre polynomials
      (legendrePolynomial 0 (x.get k) = 1) ∧
      (legendrePolynomial 1 (x.get k) = x.get k) ∧
      (legendrePolynomial 0 (y.get k) = 1) ∧
      (legendrePolynomial 1 (y.get k) = y.get k) ∧
      (legendrePolynomial 0 (z.get k) = 1) ∧
      (legendrePolynomial 1 (z.get k) = z.get k) ∧
      -- Tensor product property: 3D evaluation uses products of 1D Legendre polynomials
      (∃ series_value : Float, result.get k = series_value)⌝⦄ := by
  simp [legval3d]
  constructor
  · simp [Vector.get_ofFn]
    intro k
    constructor
    · intro h
      cases' h with h1 h
      cases' h with h2 h3
      exact base_case_helper x y z c k h1 h2 h3
    constructor
    · exact legendre_0 (x.get k)
    constructor
    · exact legendre_1 (x.get k)
    constructor
    · exact legendre_0 (y.get k)
    constructor
    · exact legendre_1 (y.get k)
    constructor
    · exact legendre_0 (z.get k)
    constructor
    · exact legendre_1 (z.get k)
    · use sumTriple x y z c k
      simp [Vector.get_ofFn]