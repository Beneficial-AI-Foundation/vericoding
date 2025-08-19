import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Laguerre polynomial L_n(x) evaluated at x.
    
    The Laguerre polynomials are defined by the recurrence:
    L_0(x) = 1
    L_1(x) = 1 - x  
    L_n(x) = ((2n-1-x)*L_{n-1}(x) - (n-1)*L_{n-2}(x)) / n for n >= 2
-/
def laguerrePolynomial (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => 1.0 - x
  | n + 2 => 
    let L_prev := laguerrePolynomial (n + 1) x
    let L_prev_prev := laguerrePolynomial n x
    let n_float := Float.ofNat (n + 2)
    ((2 * n_float - 1 - x) * L_prev - (n_float - 1) * L_prev_prev) / n_float

/-- numpy.polynomial.laguerre.lagvander3d: Pseudo-Vandermonde matrix of given degrees.

    Returns the pseudo-Vandermonde matrix of degrees `deg` and sample points `(x, y, z)`.
    The pseudo-Vandermonde matrix is defined by 
    V[..., (ydeg+1)*(zdeg+1)*i + (zdeg+1)*j + k] = L_i(x) * L_j(y) * L_k(z),
    where 0 <= i <= xdeg, 0 <= j <= ydeg, and 0 <= k <= zdeg.

    For vectors x,y,z of length n and degrees [xdeg, ydeg, zdeg], returns a matrix of shape
    (n, (xdeg + 1) * (ydeg + 1) * (zdeg + 1)) where each row contains products of Laguerre polynomials.
-/
def lagvander3d {n : Nat} (x y z : Vector Float n) (xdeg ydeg zdeg : Nat) : 
    Id (Vector (Vector Float ((xdeg + 1) * (ydeg + 1) * (zdeg + 1))) n) :=
  pure $ Vector.ofFn fun p => 
    Vector.ofFn fun col_idx => 
      let cols := (xdeg + 1) * (ydeg + 1) * (zdeg + 1)
      let i := col_idx.val / ((ydeg + 1) * (zdeg + 1))
      let j := (col_idx.val % ((ydeg + 1) * (zdeg + 1))) / (zdeg + 1)
      let k := col_idx.val % (zdeg + 1)
      laguerrePolynomial i (x.get p) * 
      laguerrePolynomial j (y.get p) * 
      laguerrePolynomial k (z.get p)

-- LLM HELPER
lemma div_mod_identity (a b c : Nat) (h1 : b > 0) (h2 : c > 0) (idx : Nat) :
    let i := idx / (b * c)
    let j := (idx % (b * c)) / c
    let k := idx % c
    idx = i * (b * c) + j * c + k := by
  simp [Nat.div_add_mod]
  rw [Nat.add_mul_div_left, Nat.add_mul_mod_self_left]
  ring

-- LLM HELPER
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get_ofFn]

/-- Specification: lagvander3d returns a 3D pseudo-Vandermonde matrix where each row
    contains products of Laguerre polynomials evaluated at corresponding points.

    Precondition: x, y, z have the same length (enforced by type)
    Postcondition:
    1. The result has shape (n, (xdeg + 1) * (ydeg + 1) * (zdeg + 1))
    2. Each element V[p, (ydeg+1)*(zdeg+1)*i + (zdeg+1)*j + k] = L_i(x[p]) * L_j(y[p]) * L_k(z[p])
    3. The ordering follows: (0,0,0), (0,0,1), ..., (0,0,zdeg), (0,1,0), ..., (xdeg,ydeg,zdeg)
    4. For the first column (i=0, j=0, k=0), all values are 1 since L_0(x) * L_0(y) * L_0(z) = 1
-/
theorem lagvander3d_spec {n : Nat} (x y z : Vector Float n) (xdeg ydeg zdeg : Nat) :
    ⦃⌜True⌝⦄
    lagvander3d x y z xdeg ydeg zdeg
    ⦃⇓result => ⌜(∀ p : Fin n, ∀ i : Fin (xdeg + 1), ∀ j : Fin (ydeg + 1), ∀ k : Fin (zdeg + 1),
                    let idx := i.val * (ydeg + 1) * (zdeg + 1) + j.val * (zdeg + 1) + k.val
                    have h_idx : idx < (xdeg + 1) * (ydeg + 1) * (zdeg + 1) := by 
                      simp [idx]
                      apply Nat.add_lt_of_lt_sub_right
                      apply Nat.add_lt_of_lt_sub_right
                      simp [Nat.mul_lt_mul_right]
                      exact i.isLt
                    (result.get p).get ⟨idx, h_idx⟩ = 
                      laguerrePolynomial i.val (x.get p) * 
                      laguerrePolynomial j.val (y.get p) * 
                      laguerrePolynomial k.val (z.get p))⌝⦄ := by
  simp [lagvander3d]
  intro p i j k
  simp [vector_get_ofFn]
  let idx := i.val * (ydeg + 1) * (zdeg + 1) + j.val * (zdeg + 1) + k.val
  have h_idx : idx < (xdeg + 1) * (ydeg + 1) * (zdeg + 1) := by 
    simp [idx]
    have h1 : i.val < xdeg + 1 := i.isLt
    have h2 : j.val < ydeg + 1 := j.isLt
    have h3 : k.val < zdeg + 1 := k.isLt
    rw [Nat.mul_assoc]
    apply Nat.add_lt_of_lt_sub_right
    apply Nat.add_lt_of_lt_sub_right  
    rw [← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right h1 (Nat.mul_pos (Nat.succ_pos ydeg) (Nat.succ_pos zdeg))
  have h_div : idx / ((ydeg + 1) * (zdeg + 1)) = i.val := by
    simp [idx]
    rw [Nat.add_mul_div_left]
    rw [Nat.div_eq_zero_iff_lt]
    simp [Nat.add_lt_iff_neg_right]
    exact Nat.mul_pos (Nat.succ_pos ydeg) (Nat.succ_pos zdeg)
  have h_mod_div : (idx % ((ydeg + 1) * (zdeg + 1))) / (zdeg + 1) = j.val := by
    simp [idx]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.add_mul_div_left]
    rw [Nat.div_eq_zero_iff_lt]
    exact k.isLt
    exact Nat.succ_pos zdeg
  have h_mod : idx % (zdeg + 1) = k.val := by
    simp [idx]
    rw [Nat.add_mod]
    rw [Nat.mul_mod]
    rw [Nat.mod_mod]
    rw [Nat.zero_mod]
    simp
    exact Nat.mod_lt _ (Nat.succ_pos zdeg)
  simp [h_div, h_mod_div, h_mod]