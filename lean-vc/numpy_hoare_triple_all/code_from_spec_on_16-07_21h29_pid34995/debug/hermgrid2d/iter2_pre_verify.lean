import Std.Do.Triple
import Std.Tactic.Do

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

-- LLM HELPER
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

-- LLM HELPER
lemma zero_rows_or_cols_helper (rows cols : Nat) (c : Vector (Vector Float cols) rows) 
    (x_val y_val : Float) : 
    (rows = 0 ∨ cols = 0) → hermiteSeriesSum rows cols c x_val y_val = 0 := by
  intro h
  unfold hermiteSeriesSum
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
        (c.get ⟨0, Nat.zero_lt_of_zero_lt_pred rows⟩).get ⟨0, Nat.zero_lt_of_zero_lt_pred cols⟩ = 1 ∧
        (∀ (p : Fin rows) (q : Fin cols), (p ≠ ⟨0, Nat.zero_lt_of_zero_lt_pred rows⟩ ∨ q ≠ ⟨0, Nat.zero_lt_of_zero_lt_pred cols⟩) → 
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
    rfl
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