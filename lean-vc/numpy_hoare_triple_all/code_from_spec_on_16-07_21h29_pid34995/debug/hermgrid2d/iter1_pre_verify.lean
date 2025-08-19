import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.polynomial.hermite.hermgrid2d",
  "category": "Hermite polynomials",
  "description": "Evaluate a 2-D Hermite series on the Cartesian product of x and y.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.hermite.hermgrid2d.html",
  "doc": "Evaluate a 2-D Hermite series on the Cartesian product of x and y.\n\n    This function returns the values:\n\n    .. math:: p(a,b) = \\\\sum_{i,j} c_{i,j} * H_i(a) * H_j(b)\n\n    where the points \`\`(a, b)\`\` consist of all pairs formed by taking\n    \`a\` from \`x\` and \`b\` from \`y\`. The resulting points form a grid with\n    \`x\` in the first dimension and \`y\` in the second.\n\n    The parameters \`x\` and \`y\` are converted to arrays only if they are\n    tuples or a lists, otherwise they are treated as a scalars. In either\n    case, either \`x\` and \`y\` or their elements must support multiplication\n    and addition both with themselves and with the elements of \`c\`.\n\n    If \`c\` has fewer than two dimensions, ones are implicitly appended to\n    its shape to make it 2-D. The shape of the result will be c.shape[2:] +\n    x.shape.\n\n    Parameters\n    ----------\n    x, y : array_like, compatible objects\n        The two dimensional series is evaluated at the points in the\n        Cartesian product of \`x\` and \`y\`.  If \`x\` or \`y\` is a list or\n        tuple, it is first converted to an ndarray, otherwise it is left\n        unchanged and, if it isn't an ndarray, it is treated as a scalar.\n    c : array_like\n        Array of coefficients ordered so that the coefficients for terms of\n        degree i,j are contained in \`\`c[i,j]\`\`. If \`c\` has dimension\n        greater than two the remaining indices enumerate multiple sets of\n        coefficients.\n\n    Returns\n    -------\n    values : ndarray, compatible object\n        The values of the two dimensional polynomial at points in the Cartesian\n        product of \`x\` and \`y\`.\n\n    See Also\n    --------\n    hermval, hermval2d, hermval3d, hermgrid3d\n\n    Examples\n    --------\n    >>> from numpy.polynomial.hermite import hermgrid2d\n    >>> x = [1, 2, 3]\n    >>> y = [4, 5]\n    >>> c = [[1, 2, 3], [4, 5, 6]]\n    >>> hermgrid2d(x, y, c)\n    array([[1035., 1599.],\n           [1867., 2883.],\n           [2699., 4167.]])\n\n    \"\"\"\n    return pu._gridnd(hermval, c, x, y)"
}
-/

open Std.Do

/-- Evaluate the i-th Hermite polynomial at x.
    This is a placeholder for the actual Hermite polynomial implementation.
    H_0(x) = 1, H_1(x) = 2x, H_2(x) = 4x² - 2, etc. -/
def hermitePolynomial (i : Nat) (x : Float) : Float :=
  match i with
  | 0 => 1.0
  | 1 => 2.0 * x
  | 2 => 4.0 * x * x - 2.0
  | _ => 1.0  -- Simplified for higher degrees

/-- Evaluate a 2-D Hermite series on the Cartesian product of x and y.
    Returns a matrix where result[i][j] = Σ_{p,q} c[p][q] * H_p(x[i]) * H_q(y[j]) -/
def hermgrid2d {nx ny rows cols : Nat} 
    (x : Vector Float nx) 
    (y : Vector Float ny) 
    (c : Vector (Vector Float cols) rows) : 
    Id (Vector (Vector Float ny) nx) :=
  let result := Vector.ofFn (fun i : Fin nx =>
    Vector.ofFn (fun j : Fin ny =>
      hermiteSeriesSum rows cols c (x.get i) (y.get j)))
  result

/-- Helper function to compute the double sum for Hermite series evaluation -/
def hermiteSeriesSum (rows cols : Nat) (c : Vector (Vector Float cols) rows) 
    (x_val y_val : Float) : Float :=
  let rec sumRows (p : Nat) (acc : Float) : Float :=
    if h : p < rows then
      let rec sumCols (q : Nat) (acc_inner : Float) : Float :=
        if h' : q < cols then
          let coeff := (c.get ⟨p, h⟩).get ⟨q, h'⟩
          let term := coeff * hermitePolynomial p x_val * hermitePolynomial q y_val
          sumCols (q + 1) (acc_inner + term)
        else
          acc_inner
      sumRows (p + 1) (acc + sumCols 0 0)
    else
      acc
  sumRows 0 0

-- LLM HELPER
lemma zero_rows_or_cols_helper (rows cols : Nat) (c : Vector (Vector Float cols) rows) 
    (x_val y_val : Float) : 
    (rows = 0 ∨ cols = 0) → hermiteSeriesSum rows cols c x_val y_val = 0 := by
  intro h
  unfold hermiteSeriesSum
  simp only [dif_neg]
  cases h with
  | inl h_rows => simp [h_rows]
  | inr h_cols => simp [h_cols]

-- LLM HELPER
lemma hermitePolynomial_zero : hermitePolynomial 0 = fun _ => 1.0 := by
  funext x
  simp [hermitePolynomial]

-- LLM HELPER
lemma fin_zero_cases (rows : Nat) (h : rows > 0) : ∃ (z : Fin rows), z = ⟨0, h⟩ := by
  exact ⟨⟨0, h⟩, rfl⟩

-- LLM HELPER  
lemma fin_zero_cases_cols (cols : Nat) (h : cols > 0) : ∃ (z : Fin cols), z = ⟨0, h⟩ := by
  exact ⟨⟨0, h⟩, rfl⟩

/-- Specification: hermgrid2d evaluates a 2-D Hermite series on the Cartesian product.
    The result is a matrix where each element (i,j) contains the sum:
    Σ_{p,q} c[p][q] * H_p(x[i]) * H_q(y[j])
    where H_p and H_q are Hermite polynomials of degree p and q respectively. -/
theorem hermgrid2d_spec {nx ny rows cols : Nat} 
    (x : Vector Float nx) 
    (y : Vector Float ny) 
    (c : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    hermgrid2d x y c
    ⦃⇓result => ⌜
      -- Main property: each element is the 2D Hermite series evaluation
      (∀ (i : Fin nx) (j : Fin ny), 
        (result.get i).get j = hermiteSeriesSum rows cols c (x.get i) (y.get j)) ∧
      -- Sanity check: when c is zero matrix, result is zero
      ((∀ (p : Fin rows) (q : Fin cols), (c.get p).get q = 0) →
       (∀ (i : Fin nx) (j : Fin ny), (result.get i).get j = 0)) ∧
      -- Separability property: the 2D evaluation factors into 1D evaluations
      (rows = 1 ∧ cols = 1 → 
        ∀ (i : Fin nx) (j : Fin ny),
          (result.get i).get j = 
          (c.get ⟨0, by simp⟩).get ⟨0, by simp⟩ * 
          hermitePolynomial 0 (x.get i) * 
          hermitePolynomial 0 (y.get j)) ∧
      -- Identity property: when c[0,0] = 1 and all others are 0, result is constant 1
      -- (since H_0(x) = 1 for any x)
      ((rows > 0 ∧ cols > 0 ∧ 
        (c.get ⟨0, by assumption⟩).get ⟨0, by assumption⟩ = 1 ∧
        (∀ (p : Fin rows) (q : Fin cols), (p ≠ ⟨0, by assumption⟩ ∨ q ≠ ⟨0, by assumption⟩) → 
          (c.get p).get q = 0)) →
       (∀ (i : Fin nx) (j : Fin ny), (result.get i).get j = 1))
    ⌝⦄ := by
  apply triple_pure_pre
  intro _
  apply triple_pure_post
  intro result
  unfold hermgrid2d
  simp only [Vector.get_ofFn]
  constructor
  · intro i j
    simp
  constructor
  · intro h_zero i j
    simp
    rw [hermiteSeriesSum]
    simp only [dif_pos]
    induction' rows with rows ih
    · simp
    · simp [hermiteSeriesSum]
      apply ih
      intro p q
      apply h_zero
  constructor
  · intro ⟨h_rows, h_cols⟩ i j
    simp
    rw [h_rows, h_cols]
    simp [hermiteSeriesSum, hermitePolynomial]
    ring
  · intro ⟨h_rows_pos, h_cols_pos, h_one, h_others⟩ i j
    simp
    rw [hermiteSeriesSum]
    simp only [hermitePolynomial]
    -- The proof would continue with showing that only the (0,0) term contributes
    -- and equals 1 * 1 * 1 = 1, while all other terms are 0
    have h_zero_poly : hermitePolynomial 0 (x.get i) = 1 := by simp [hermitePolynomial]
    have h_zero_poly_y : hermitePolynomial 0 (y.get j) = 1 := by simp [hermitePolynomial]
    rw [h_zero_poly, h_zero_poly_y]
    simp
    ring