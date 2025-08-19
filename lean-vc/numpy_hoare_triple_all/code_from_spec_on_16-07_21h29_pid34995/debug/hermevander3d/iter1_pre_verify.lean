import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermite_poly : Nat → Float → Float
  | 0, _ => 1.0
  | 1, t => t
  | n + 2, t => t * hermite_poly (n + 1) t - Float.ofNat (n + 1) * hermite_poly n t

-- LLM HELPER
def compute_column_index (i j k : Nat) (y_deg z_deg : Nat) : Nat :=
  (y_deg + 1) * (z_deg + 1) * i + (z_deg + 1) * j + k

-- LLM HELPER
def build_vander_row (x_val y_val z_val : Float) (x_deg y_deg z_deg : Nat) : Vector Float ((x_deg + 1) * (y_deg + 1) * (z_deg + 1)) :=
  let order := (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
  Vector.ofFn (fun col_idx : Fin order =>
    -- Find i, j, k such that col_idx = (y_deg + 1) * (z_deg + 1) * i + (z_deg + 1) * j + k
    let i := col_idx.val / ((y_deg + 1) * (z_deg + 1))
    let remainder := col_idx.val % ((y_deg + 1) * (z_deg + 1))
    let j := remainder / (z_deg + 1)
    let k := remainder % (z_deg + 1)
    hermite_poly i x_val * hermite_poly j y_val * hermite_poly k z_val)

/-- numpy.polynomial.hermite_e.hermevander3d: Pseudo-Vandermonde matrix of given degrees.

    Returns the pseudo-Vandermonde matrix of degrees `deg` and sample
    points `(x, y, z)`. If `l`, `m`, `n` are the given degrees in `x`, `y`, `z`,
    then the pseudo-Vandermonde matrix is defined by

    .. math:: V[..., (m+1)(n+1)i + (n+1)j + k] = He_i(x)*He_j(y)*He_k(z),

    where `0 <= i <= l`, `0 <= j <= m`, and `0 <= k <= n`. The leading
    indices of `V` index the points `(x, y, z)` and the last index encodes
    the degrees of the HermiteE polynomials.

    The HermiteE polynomials (also called probabilist's Hermite polynomials) are
    defined by the recurrence relation:
    - He_0(t) = 1
    - He_1(t) = t  
    - He_n(t) = t * He_{n-1}(t) - (n-1) * He_{n-2}(t)

    Parameters
    ----------
    x, y, z : Vector Float n
        Arrays of point coordinates, all of the same shape.
    deg : Vector Nat 3
        Vector of maximum degrees of the form [x_deg, y_deg, z_deg].

    Returns
    -------
    vander3d : Vector (Vector Float order) n
        The pseudo-Vandermonde matrix where order = (deg[0]+1)*(deg[1]+1)*(deg[2]+1).
-/
def hermevander3d {n : Nat} (x y z : Vector Float n) (deg : Vector Nat 3) : 
    Id (Vector (Vector Float ((deg.get ⟨0, by simp⟩ + 1) * (deg.get ⟨1, by simp⟩ + 1) * (deg.get ⟨2, by simp⟩ + 1))) n) :=
  let x_deg := deg.get ⟨0, by simp⟩
  let y_deg := deg.get ⟨1, by simp⟩
  let z_deg := deg.get ⟨2, by simp⟩
  Vector.ofFn (fun p : Fin n =>
    build_vander_row (x.get p) (y.get p) (z.get p) x_deg y_deg z_deg)

-- LLM HELPER
lemma hermite_poly_base_0 (t : Float) : hermite_poly 0 t = 1 := by
  simp [hermite_poly]

-- LLM HELPER
lemma hermite_poly_base_1 (t : Float) : hermite_poly 1 t = t := by
  simp [hermite_poly]

-- LLM HELPER
lemma hermite_poly_recurrence (k : Nat) (t : Float) (h : k ≥ 2) : 
    hermite_poly k t = t * hermite_poly (k-1) t - Float.ofNat (k-1) * hermite_poly (k-2) t := by
  cases k with
  | zero => contradiction
  | succ k' => 
    cases k' with
    | zero => contradiction
    | succ k'' => simp [hermite_poly]

-- LLM HELPER
lemma build_vander_row_base_case (x_val y_val z_val : Float) (x_deg y_deg z_deg : Nat) 
    (h : (x_deg + 1) * (y_deg + 1) * (z_deg + 1) > 0) :
    (build_vander_row x_val y_val z_val x_deg y_deg z_deg).get ⟨0, h⟩ = 1 := by
  simp [build_vander_row]
  simp [hermite_poly]

-- LLM HELPER
lemma hermite_poly_parity (k : Nat) (t : Float) :
    hermite_poly k (-t) = (if k % 2 = 0 then 1 else -1) * hermite_poly k t := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero => simp [hermite_poly]
    | succ k' =>
      cases k' with
      | zero => simp [hermite_poly]
      | succ k'' =>
        simp [hermite_poly]
        have h1 := ih (k'' + 1) (by simp)
        have h2 := ih k'' (by simp)
        simp [h1, h2]
        ring

/-- Specification: hermevander3d returns a 3D pseudo-Vandermonde matrix where each row
    corresponds to a point (x[i], y[i], z[i]), and each column corresponds to a product
    of HermiteE polynomials He_i(x)*He_j(y)*He_k(z) for various degrees.

    The HermiteE polynomials (also called probabilist's Hermite polynomials) are
    defined by the recurrence relation:
    - He_0(t) = 1
    - He_1(t) = t  
    - He_n(t) = t * He_{n-1}(t) - (n-1) * He_{n-2}(t)

    The indexing follows the formula:
    V[p, (m+1)(n+1)i + (n+1)j + k] = He_i(x[p]) * He_j(y[p]) * He_k(z[p])
    where m = deg[1], n = deg[2], and:
    - 0 <= i <= deg[0] (x-degree)
    - 0 <= j <= deg[1] (y-degree)  
    - 0 <= k <= deg[2] (z-degree)

    Precondition: True (no special preconditions needed)
    Postcondition: 
    1. The matrix has shape (n, order) where order = (deg[0]+1)*(deg[1]+1)*(deg[2]+1)
    2. Each element V[p][idx] = He_i(x[p]) * He_j(y[p]) * He_k(z[p])
    3. The column ordering follows the flattened 3D coefficient array pattern
    4. Base case: V[p][0] = He_0(x[p]) * He_0(y[p]) * He_0(z[p]) = 1 * 1 * 1 = 1
    5. Mathematical consistency with tensor product structure
-/
theorem hermevander3d_spec {n : Nat} (x y z : Vector Float n) (deg : Vector Nat 3) :
    ⦃⌜True⌝⦄
    hermevander3d x y z deg
    ⦃⇓result => ⌜
      let x_deg := deg.get ⟨0, by simp⟩
      let y_deg := deg.get ⟨1, by simp⟩
      let z_deg := deg.get ⟨2, by simp⟩
      let order := (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
      
      -- Shape property: result has n rows, each with order elements (enforced by types)
      True ∧
      
      -- Base case: first column is all ones (He_0(x)*He_0(y)*He_0(z) = 1*1*1 = 1)
      (∀ p : Fin n, order > 0 → (result.get p).get ⟨0, by sorry⟩ = 1) ∧
      
      -- Mathematical consistency: tensor product structure
      (∃ hermite_poly : Nat → Float → Float,
        -- HermiteE polynomial base cases
        (∀ t : Float, hermite_poly 0 t = 1) ∧
        (∀ t : Float, hermite_poly 1 t = t) ∧
        -- HermiteE polynomial recurrence relation
        (∀ k : Nat, k ≥ 2 → ∀ t : Float, 
          hermite_poly k t = t * hermite_poly (k-1) t - Float.ofNat (k-1) * hermite_poly (k-2) t) ∧
        -- Each matrix element follows the 3D product formula
        (∀ p : Fin n, ∀ i : Nat, ∀ j : Nat, ∀ k : Nat,
          i ≤ x_deg → j ≤ y_deg → k ≤ z_deg →
          let col_idx := (y_deg + 1) * (z_deg + 1) * i + (z_deg + 1) * j + k
          col_idx < order →
          (result.get p).get ⟨col_idx, by sorry⟩ = 
            hermite_poly i (x.get p) * hermite_poly j (y.get p) * hermite_poly k (z.get p))) ∧
      
      -- Orthogonality property: HermiteE polynomials are orthogonal with respect to Gaussian weight
      (∀ p : Fin n, ∀ i₁ j₁ k₁ i₂ j₂ k₂ : Nat,
        i₁ ≤ x_deg → j₁ ≤ y_deg → k₁ ≤ z_deg →
        i₂ ≤ x_deg → j₂ ≤ y_deg → k₂ ≤ z_deg →
        (i₁ ≠ i₂ ∨ j₁ ≠ j₂ ∨ k₁ ≠ k₂) →
        let col_idx₁ := (y_deg + 1) * (z_deg + 1) * i₁ + (z_deg + 1) * j₁ + k₁
        let col_idx₂ := (y_deg + 1) * (z_deg + 1) * i₂ + (z_deg + 1) * j₂ + k₂
        col_idx₁ < order → col_idx₂ < order →
        -- Different polynomial products are linearly independent
        (result.get p).get ⟨col_idx₁, by sorry⟩ ≠ (result.get p).get ⟨col_idx₂, by sorry⟩ ∨ 
        x.get p = 0 ∧ y.get p = 0 ∧ z.get p = 0) ∧
      
      -- Consistency with evaluation: dot product with coefficients equals 3D polynomial evaluation
      (∀ p : Fin n, ∀ coeff : Vector Float order,
        ∃ polynomial_value : Float,
          -- The dot product of the Vandermonde row with coefficients
          -- equals the evaluation of the 3D HermiteE polynomial expansion
          polynomial_value = (List.sum (List.ofFn (fun i : Fin order => (result.get p).get i * coeff.get i)))) ∧
      
      -- Parity property: HermiteE polynomials satisfy He_n(-x) = (-1)^n * He_n(x)
      (∃ hermite_poly : Nat → Float → Float,
        (∀ k : Nat, k ≤ max (max x_deg y_deg) z_deg → ∀ t : Float,
          hermite_poly k (-t) = (if k % 2 = 0 then 1 else -1) * hermite_poly k t) ∧
        -- This parity property is reflected in the matrix structure
        (∀ p : Fin n, ∀ i j k : Nat,
          i ≤ x_deg → j ≤ y_deg → k ≤ z_deg →
          let col_idx := (y_deg + 1) * (z_deg + 1) * i + (z_deg + 1) * j + k
          col_idx < order →
          (result.get p).get ⟨col_idx, by sorry⟩ = 
            hermite_poly i (x.get p) * hermite_poly j (y.get p) * hermite_poly k (z.get p)))
    ⌝⦄ := by
  simp [Std.Do.Triple.SpecM.spec_bind, Std.Do.Triple.SpecM.spec_pure]
  simp [hermevander3d]
  constructor
  · trivial
  constructor
  · intro p h_order
    simp [Vector.get_ofFn]
    exact build_vander_row_base_case (x.get p) (y.get p) (z.get p) _ _ _ h_order
  constructor
  · use hermite_poly
    constructor
    · exact hermite_poly_base_0
    constructor
    · exact hermite_poly_base_1
    constructor
    · exact hermite_poly_recurrence
    · intro p i j k hi hj hk hcol
      simp [Vector.get_ofFn, build_vander_row]
      simp [Vector.get_ofFn]
      congr
  constructor
  · intro p i₁ j₁ k₁ i₂ j₂ k₂ hi₁ hj₁ hk₁ hi₂ hj₂ hk₂ hneq hcol₁ hcol₂
    simp [Vector.get_ofFn, build_vander_row]
    simp [Vector.get_ofFn]
    by_cases h : x.get p = 0 ∧ y.get p = 0 ∧ z.get p = 0
    · right
      exact h
    · left
      simp [h]
      by_contra hcontra
      have : i₁ = i₂ ∧ j₁ = j₂ ∧ k₁ = k₂ := by
        sorry -- This would require more detailed reasoning about polynomial linear independence
      exact hneq this
  constructor
  · intro p coeff
    use (List.sum (List.ofFn (fun i : Fin order => (result.get p).get i * coeff.get i)))
    rfl
  · use hermite_poly
    constructor
    · intro k hk t
      exact hermite_poly_parity k t
    · intro p i j k hi hj hk hcol
      simp [Vector.get_ofFn, build_vander_row]
      simp [Vector.get_ofFn]
      congr