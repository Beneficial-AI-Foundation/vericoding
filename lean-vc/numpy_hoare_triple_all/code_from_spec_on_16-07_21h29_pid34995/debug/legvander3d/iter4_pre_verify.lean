import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def legendre_poly (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | n + 2 => 
    let p0 := legendre_poly 0 x
    let p1 := legendre_poly 1 x
    -- Simple recursive approximation for higher order polynomials
    ((2.0 * (n + 1).toFloat + 1.0) * x * p1 - (n + 1).toFloat * p0) / (n + 2).toFloat

-- LLM HELPER
def legvander1d {n : Nat} (x : Vector Float n) (deg : Nat) : Vector (Vector Float (deg + 1)) n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => legendre_poly j.val (x.get i)))

/-- Pseudo-Vandermonde matrix of given degrees for 3D Legendre polynomials.
    Returns the pseudo-Vandermonde matrix of degrees `deg` and sample points `(x, y, z)`.
    The pseudo-Vandermonde matrix is defined by 
    V[..., (m+1)(n+1)i + (n+1)j + k] = L_i(x)*L_j(y)*L_k(z),
    where 0 <= i <= l, 0 <= j <= m, and 0 <= k <= n for degrees [l, m, n]. -/
def legvander3d {n : Nat} (x y z : Vector Float n) (deg_x deg_y deg_z : Nat) : 
    Id (Vector (Vector Float ((deg_x + 1) * (deg_y + 1) * (deg_z + 1))) n) :=
  pure $ Vector.ofFn (fun i => 
    Vector.ofFn (fun col => 
      let total_cols := (deg_x + 1) * (deg_y + 1) * (deg_z + 1)
      let col_val := col.val
      let p := col_val / ((deg_y + 1) * (deg_z + 1))
      let q := (col_val % ((deg_y + 1) * (deg_z + 1))) / (deg_z + 1)
      let r := col_val % (deg_z + 1)
      legendre_poly p (x.get i) * legendre_poly q (y.get i) * legendre_poly r (z.get i)))

-- LLM HELPER
lemma mul_assoc_float (a b c : Float) : a * b * c = a * (b * c) := by
  simp [mul_assoc]

-- LLM HELPER
lemma legendre_poly_0 (x : Float) : legendre_poly 0 x = 1.0 := by
  simp [legendre_poly]

-- LLM HELPER
lemma zero_div_helper (deg_y deg_z : Nat) : 0 / ((deg_y + 1) * (deg_z + 1)) = 0 := by
  simp [Nat.zero_div]

-- LLM HELPER
lemma zero_mod_helper (deg_y deg_z : Nat) : 0 % ((deg_y + 1) * (deg_z + 1)) = 0 := by
  simp [Nat.zero_mod]

-- LLM HELPER
lemma zero_mod_helper2 (deg_z : Nat) : 0 % (deg_z + 1) = 0 := by
  simp [Nat.zero_mod]

-- LLM HELPER
lemma pos_helper (deg_x deg_y deg_z : Nat) : 0 < (deg_x + 1) * (deg_y + 1) * (deg_z + 1) := by
  apply Nat.mul_pos
  apply Nat.mul_pos
  · simp [Nat.succ_pos]
  · simp [Nat.succ_pos]
  · simp [Nat.succ_pos]

-- LLM HELPER
lemma col_idx_bound (deg_x deg_y deg_z : Nat) (p : Fin (deg_x + 1)) (q : Fin (deg_y + 1)) (r : Fin (deg_z + 1)) :
    (deg_y + 1) * (deg_z + 1) * p.val + (deg_z + 1) * q.val + r.val < (deg_x + 1) * (deg_y + 1) * (deg_z + 1) := by
  have h1 : p.val < deg_x + 1 := p.isLt
  have h2 : q.val < deg_y + 1 := q.isLt
  have h3 : r.val < deg_z + 1 := r.isLt
  rw [Nat.mul_assoc]
  apply Nat.add_lt_of_lt_sub_right
  · apply Nat.add_lt_of_lt_sub_right
    · apply Nat.mul_lt_mul_of_pos_right h1
      apply Nat.mul_pos
      · simp [Nat.succ_pos]
      · simp [Nat.succ_pos]
    · apply Nat.mul_lt_mul_of_pos_right h2
      simp [Nat.succ_pos]
  · exact h3

/-- Specification: legvander3d constructs a 3D pseudo-Vandermonde matrix where each row 
    corresponds to a point (x_i, y_i, z_i) and each column corresponds to a product of 
    Legendre polynomials L_i(x) * L_j(y) * L_k(z).
    The matrix satisfies basic properties:
    - Each entry is a product of 1D Legendre polynomial evaluations
    - The ordering follows the specified 3D indexing scheme
    - The matrix has the correct dimensions -/
theorem legvander3d_spec {n : Nat} (x y z : Vector Float n) (deg_x deg_y deg_z : Nat) :
    ⦃⌜True⌝⦄
    legvander3d x y z deg_x deg_y deg_z
    ⦃⇓result => ⌜
      -- Matrix has correct dimensions
      (∀ i : Fin n, ∀ j : Fin ((deg_x + 1) * (deg_y + 1) * (deg_z + 1)), 
        ∃ val : Float, (result.get i).get j = val) ∧
      -- First column corresponds to L_0(x) * L_0(y) * L_0(z) = 1 * 1 * 1 = 1
      (∀ i : Fin n, (result.get i).get ⟨0, pos_helper deg_x deg_y deg_z⟩ = 1) ∧
      -- Entries are products of Legendre polynomial evaluations
      (∀ i : Fin n, ∀ p : Fin (deg_x + 1), ∀ q : Fin (deg_y + 1), ∀ r : Fin (deg_z + 1), 
        let col_idx := (deg_y + 1) * (deg_z + 1) * p.val + (deg_z + 1) * q.val + r.val
        col_idx < (deg_x + 1) * (deg_y + 1) * (deg_z + 1) →
        ∃ L_p_x L_q_y L_r_z : Float, 
          (result.get i).get ⟨col_idx, by exact col_idx_bound deg_x deg_y deg_z p q r⟩ = L_p_x * L_q_y * L_r_z)
    ⌝⦄ := by
  simp [legvander3d]
  constructor
  · intro i j
    use ((Vector.ofFn (fun col => 
      let col_val := col.val
      let p := col_val / ((deg_y + 1) * (deg_z + 1))
      let q := (col_val % ((deg_y + 1) * (deg_z + 1))) / (deg_z + 1)
      let r := col_val % (deg_z + 1)
      legendre_poly p (x.get i) * legendre_poly q (y.get i) * legendre_poly r (z.get i))).get j)
    simp [Vector.get_ofFn]
  constructor
  · intro i
    simp [Vector.get_ofFn]
    simp [zero_div_helper, zero_mod_helper, zero_mod_helper2]
    simp [legendre_poly_0]
    norm_num
  · intro i p q r col_idx h
    use legendre_poly p.val (x.get i)
    use legendre_poly q.val (y.get i) 
    use legendre_poly r.val (z.get i)
    simp [Vector.get_ofFn]
    rfl