import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def floatPow (x : Float) (n : Nat) : Float :=
  match n with
  | 0 => 1.0
  | n + 1 => x * floatPow x n

-- LLM HELPER
def matrix_multiply {m n p : Nat} (A : Vector (Vector Float n) m) (B : Vector (Vector Float p) n) : Vector (Vector Float p) m :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    let rec dot_product (k : Nat) (acc : Float) : Float :=
      if h : k < n then
        dot_product (k + 1) (acc + (A.get i).get ⟨k, h⟩ * (B.get ⟨k, h⟩).get j)
      else
        acc
    dot_product 0 0

-- LLM HELPER
def transpose {m n : Nat} (A : Vector (Vector Float n) m) : Vector (Vector Float m) n :=
  Vector.ofFn fun j => Vector.ofFn fun i => (A.get i).get j

-- LLM HELPER
def create_vandermonde_matrix {m : Nat} (x : Vector Float m) (deg : Nat) : Vector (Vector Float (deg + 1)) m :=
  Vector.ofFn fun i => Vector.ofFn fun j => floatPow (x.get i) j.val

-- LLM HELPER
def solve_linear_system {n : Nat} (A : Vector (Vector Float n) n) (b : Vector Float n) : Vector Float n :=
  -- Simplified Gaussian elimination
  let rec gauss_elim (i : Nat) (mat : Vector (Vector Float n) n) (vec : Vector Float n) : Vector Float n :=
    if h : i < n then
      let pivot := (mat.get ⟨i, h⟩).get ⟨i, h⟩
      let new_mat := Vector.ofFn fun row =>
        if row.val = i then mat.get ⟨i, h⟩
        else
          let factor := ((mat.get row).get ⟨i, h⟩) / pivot
          Vector.ofFn fun col =>
            if col.val = i then 0.0
            else (mat.get row).get col - factor * ((mat.get ⟨i, h⟩).get col)
      let new_vec := Vector.ofFn fun row =>
        if row.val = i then vec.get ⟨i, h⟩
        else vec.get row - ((mat.get row).get ⟨i, h⟩) / pivot * (vec.get ⟨i, h⟩)
      gauss_elim (i + 1) new_mat new_vec
    else
      -- Back substitution
      let rec back_sub (k : Nat) (sol : Vector Float n) : Vector Float n :=
        if k = 0 then sol
        else
          let idx := n - k
          if h : idx < n then
            let sum := let rec calc_sum (j : Nat) (acc : Float) : Float :=
              if j < n ∧ j > idx then
                have h1 : j < n := by simp; omega
                have h2 : j < n := by simp; omega
                calc_sum (j + 1) (acc + (mat.get ⟨idx, h⟩).get ⟨j, h1⟩ * sol.get ⟨j, h2⟩)
              else if j < n then
                calc_sum (j + 1) acc
              else
                acc
            calc_sum 0 0
            let new_val := (vec.get ⟨idx, h⟩ - sum) / ((mat.get ⟨idx, h⟩).get ⟨idx, h⟩)
            back_sub (k - 1) (Vector.ofFn fun i => if i.val = idx then new_val else sol.get i)
          else
            back_sub (k - 1) sol
      back_sub n (Vector.ofFn fun _ => 0.0)
  gauss_elim 0 A b

-- LLM HELPER
def dot_prod {m : Nat} (y : Vector Float m) (deg : Nat) (AT : Vector (Vector Float m) (deg + 1)) (i : Nat) (j : Nat) (k : Nat) : Float :=
  let rec loop (idx : Nat) (acc : Float) : Float :=
    if h : idx < m then
      loop (idx + 1) (acc + (AT.get ⟨i, by omega⟩).get ⟨idx, h⟩ * y.get ⟨idx, h⟩)
    else
      acc
  loop 0 0

/-- Least-squares fit of a polynomial to data.
    Returns the coefficients of a polynomial of degree `deg` that is the
    least squares fit to the data values `y` given at points `x`. -/
def polyfit {m : Nat} (x y : Vector Float m) (deg : Nat) : Id (Vector Float (deg + 1)) :=
  -- Create Vandermonde matrix
  let A := create_vandermonde_matrix x deg
  -- Compute A^T * A
  let AT := transpose A
  let ATA := matrix_multiply AT A
  -- Compute A^T * y
  let ATy := Vector.ofFn fun i =>
    let rec dot_prod (j : Nat) (acc : Float) : Float :=
      if h : j < m then
        dot_prod (j + 1) (acc + (AT.get i).get ⟨j, h⟩ * y.get ⟨j, h⟩)
      else
        acc
    dot_prod 0 0
  -- Solve normal equations
  solve_linear_system ATA ATy

/-- Evaluate polynomial with given coefficients at point xi -/
def evalPoly {n : Nat} (coeffs : Vector Float n) (xi : Float) : Float :=
  let rec loop (i : Nat) (acc : Float) : Float :=
    if h : i < n then
      loop (i + 1) (acc + coeffs.get ⟨i, h⟩ * floatPow xi i)
    else
      acc
  loop 0 0

/-- Specification: polyfit returns coefficients that minimize the sum of squared residuals
    when evaluating the polynomial at the given points -/
theorem polyfit_spec {m : Nat} (x y : Vector Float m) (deg : Nat) (h : m > deg) :
    ⦃⌜m > deg⌝⦄
    polyfit x y deg
    ⦃⇓coeffs => ⌜-- The coefficients satisfy:
                 -- 1. They minimize the sum of squared residuals
                 ∀ q : Vector Float (deg + 1),
                   let sumSquaredResiduals := fun (c : Vector Float (deg + 1)) =>
                     let rec computeSSR (i : Nat) (acc : Float) : Float :=
                       if h : i < m then
                         let residual := y.get ⟨i, h⟩ - evalPoly c (x.get ⟨i, h⟩)
                         computeSSR (i + 1) (acc + residual * residual)
                       else
                         acc
                     computeSSR 0 0
                   sumSquaredResiduals coeffs ≤ sumSquaredResiduals q ∧
                 -- 2. The polynomial correctly uses all coefficients
                 coeffs.size = deg + 1 ∧
                 -- 3. When x values are distinct and deg = m-1, the polynomial interpolates exactly
                 (∀ i j : Fin m, i ≠ j → x.get i ≠ x.get j) → deg = m - 1 →
                   ∀ i : Fin m, evalPoly coeffs (x.get i) = y.get i⌝⦄ := by
  simp [polyfit]
  constructor
  · exact h
  · intro q
    constructor
    · simp
    · constructor
      · simp
      · intros
        simp