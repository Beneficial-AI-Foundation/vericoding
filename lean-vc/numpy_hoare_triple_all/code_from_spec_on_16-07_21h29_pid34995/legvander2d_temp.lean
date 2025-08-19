import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def legendre_poly (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | k + 2 => 
    let p0 := legendre_poly 0 x
    let p1 := legendre_poly 1 x
    -- Use recurrence relation: (n+1)P_{n+1}(x) = (2n+1)xP_n(x) - nP_{n-1}(x)
    let rec helper (prev_prev prev : Float) (curr_n : Nat) : Float :=
      if curr_n = k + 2 then
        let coeff1 := (2.0 * (curr_n - 1).toFloat + 1.0 : Float)
        let coeff2 := (curr_n - 1).toFloat
        (coeff1 * x * prev - coeff2 * prev_prev) / curr_n.toFloat
      else
        let coeff1 := (2.0 * (curr_n - 1).toFloat + 1.0 : Float)
        let coeff2 := (curr_n - 1).toFloat
        let next := (coeff1 * x * prev - coeff2 * prev_prev) / curr_n.toFloat
        helper prev next (curr_n + 1)
    termination_by (k + 2) - curr_n
    decreasing_by 
      simp_wf
      have h_pos : curr_n < k + 2 := by
        by_contra h
        simp at h
        exact absurd h ‹¬curr_n = k + 2›
      omega
    helper p0 p1 2

-- LLM HELPER
def nat_nonzero_mul (a b : Nat) : a > 0 → b > 0 → a * b > 0 := by
  intros ha hb
  exact Nat.mul_pos ha hb

/-- Pseudo-Vandermonde matrix of given degrees for 2D Legendre polynomials.
    Returns the pseudo-Vandermonde matrix of degrees `deg` and sample points `(x, y)`.
    The pseudo-Vandermonde matrix is defined by V[..., (deg[1] + 1)*i + j] = L_i(x) * L_j(y),
    where 0 <= i <= deg[0] and 0 <= j <= deg[1]. -/
def legvander2d {n : Nat} (x y : Vector Float n) (deg_x deg_y : Nat) : Id (Vector (Vector Float ((deg_x + 1) * (deg_y + 1))) n) :=
  pure <| Vector.ofFn fun i =>
    Vector.ofFn fun j =>
      let p := j.val / (deg_y + 1)
      let q := j.val % (deg_y + 1)
      legendre_poly p (x.get i) * legendre_poly q (y.get i)

-- LLM HELPER
theorem nat_mul_add_lt {a b c : Nat} (ha : a < b) (hc : c < b) : a * b + c < b * b := by
  have h1 : a * b < b * b := by
    rw [Nat.mul_lt_mul_right]
    exact ha
  have h_pos : 0 < b := Nat.zero_lt_of_ne_zero (fun h => by rw [h] at ha; exact Nat.not_lt_zero a ha)
  have h2 : a * b + c < b * b := by
    have : c < b * b - a * b := by
      rw [Nat.sub_pos_iff_lt] at h1
      have : b * b - a * b ≥ b := by
        rw [← Nat.mul_sub_right_distrib]
        have : b - a > 0 := Nat.sub_pos_of_lt ha
        have : b * (b - a) ≥ b := by
          rw [Nat.mul_comm]
          exact Nat.le_mul_of_pos_left h_pos
        exact this
      exact Nat.lt_of_le_of_lt (Nat.le_of_lt hc) this
    exact Nat.add_lt_of_lt_sub this h1
  exact h2

-- LLM HELPER  
theorem col_idx_bound (p : Fin (deg_x + 1)) (q : Fin (deg_y + 1)) : 
  (deg_y + 1) * p.val + q.val < (deg_x + 1) * (deg_y + 1) := by
  have h1 : p.val < deg_x + 1 := p.isLt
  have h2 : q.val < deg_y + 1 := q.isLt
  have h3 : (deg_y + 1) * p.val < (deg_x + 1) * (deg_y + 1) := by
    rw [Nat.mul_comm (deg_x + 1)]
    rw [Nat.mul_lt_mul_left]
    constructor
    · exact h1
    · exact Nat.zero_lt_succ _
  have h4 : (deg_y + 1) * p.val + q.val < (deg_x + 1) * (deg_y + 1) := by
    have : q.val < (deg_x + 1) * (deg_y + 1) - (deg_y + 1) * p.val := by
      rw [← Nat.mul_sub_left_distrib]
      rw [Nat.mul_comm (deg_x + 1)]
      have : deg_x + 1 - p.val > 0 := Nat.sub_pos_of_lt h1
      have : (deg_y + 1) * (deg_x + 1 - p.val) ≥ deg_y + 1 := by
        rw [Nat.mul_comm]
        exact Nat.le_mul_of_pos_left (Nat.zero_lt_succ _)
      exact Nat.lt_of_le_of_lt (Nat.le_of_lt h2) this
    have h_sub : (deg_y + 1) * p.val < (deg_x + 1) * (deg_y + 1) := h3
    exact Nat.add_lt_of_lt_sub h_sub this
  exact h4

-- LLM HELPER
theorem legendre_poly_zero : ∀ x, legendre_poly 0 x = 1.0 := by
  intro x
  unfold legendre_poly
  rfl

-- LLM HELPER
theorem mul_pos_helper : (deg_x + 1) * (deg_y + 1) > 0 := by
  exact Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)

-- LLM HELPER
theorem div_mod_unique (a b : Nat) (hb : b > 0) : a = b * (a / b) + (a % b) := by
  exact Nat.div_add_mod a b

/-- Specification: legvander2d constructs a 2D pseudo-Vandermonde matrix where each row 
    corresponds to a point (x_i, y_i) and each column corresponds to a product of 
    Legendre polynomials L_i(x) * L_j(y).
    The matrix satisfies basic properties:
    - Each entry is a product of 1D Legendre polynomial evaluations
    - The ordering follows the specified indexing scheme
    - The matrix has the correct dimensions -/
theorem legvander2d_spec {n : Nat} (x y : Vector Float n) (deg_x deg_y : Nat) :
    ⦃⌜True⌝⦄
    legvander2d x y deg_x deg_y
    ⦃⇓result => ⌜
      -- Matrix has correct dimensions
      (∀ i : Fin n, ∀ j : Fin ((deg_x + 1) * (deg_y + 1)), ∃ val : Float, (result.get i).get j = val) ∧
      -- First column corresponds to L_0(x) * L_0(y) = 1 * 1 = 1
      (∀ i : Fin n, (result.get i).get ⟨0, mul_pos_helper⟩ = 1) ∧
      -- Entries are products of Legendre polynomial evaluations
      (∀ i : Fin n, ∀ p : Fin (deg_x + 1), ∀ q : Fin (deg_y + 1), 
        let col_idx := (deg_y + 1) * p.val + q.val
        col_idx < (deg_x + 1) * (deg_y + 1) →
        ∃ L_p_x L_q_y : Float, 
          (result.get i).get ⟨col_idx, col_idx_bound p q⟩ = L_p_x * L_q_y)
    ⌝⦄ := by
  simp [legvander2d]
  constructor
  · intro i j
    use (Vector.ofFn fun j => let p := j.val / (deg_y + 1); let q := j.val % (deg_y + 1); legendre_poly p (x.get i) * legendre_poly q (y.get i)).get j
    rfl
  constructor
  · intro i
    simp [Vector.get_ofFn]
    have h1 : 0 / (deg_y + 1) = 0 := Nat.zero_div _
    have h2 : 0 % (deg_y + 1) = 0 := Nat.zero_mod _
    rw [h1, h2]
    rw [legendre_poly_zero, legendre_poly_zero]
    norm_num
  · intro i p q col_idx h
    use legendre_poly p.val (x.get i), legendre_poly q.val (y.get i)
    simp [Vector.get_ofFn]
    have h1 : col_idx / (deg_y + 1) = p.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_succ _)]
      rw [Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ _)] at q.isLt
      exact Nat.div_eq_of_lt q.isLt
    have h2 : col_idx % (deg_y + 1) = q.val := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt q.isLt
    rw [h1, h2]