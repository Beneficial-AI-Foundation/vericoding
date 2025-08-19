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
    let coeff := (2 * (n + 2) - 1 : Float) - x
    (coeff * L_prev - ((n + 1) : Float) * L_prev_prev) / ((n + 2) : Float)

-- LLM HELPER
def buildResult (n : Nat) (xdeg ydeg : Nat) (x y : Vector Float n) : 
    Vector (Vector Float ((xdeg + 1) * (ydeg + 1))) n :=
  let resultArray : Array (Vector Float ((xdeg + 1) * (ydeg + 1))) := 
    Array.replicate n (Vector.mk (Array.replicate ((xdeg + 1) * (ydeg + 1)) 0.0) rfl)
  let finalArray := resultArray.mapIdx (fun k _ =>
    let rowArray := Array.replicate ((xdeg + 1) * (ydeg + 1)) 0.0
    let finalRowArray := rowArray.mapIdx (fun idx _ =>
      let i := idx / (ydeg + 1)
      let j := idx % (ydeg + 1)
      laguerrePolynomial i (x.get ⟨k, by
        have h : k < n := by
          simp [Array.size_mapIdx, Array.size_replicate] at *
          sorry
        exact h
      ⟩) * 
      laguerrePolynomial j (y.get ⟨k, by
        have h : k < n := by
          simp [Array.size_mapIdx, Array.size_replicate] at *
          sorry
        exact h
      ⟩)
    )
    Vector.mk finalRowArray rfl
  )
  have h_size : finalArray.size = n := by
    simp [Array.size_mapIdx, Array.size_replicate]
  Vector.mk finalArray h_size

/-- numpy.polynomial.laguerre.lagvander2d: Pseudo-Vandermonde matrix of given degrees.

    Returns the pseudo-Vandermonde matrix of degrees `deg` and sample points `(x, y)`.
    The pseudo-Vandermonde matrix is defined by V[..., (deg[1] + 1)*i + j] = L_i(x) * L_j(y),
    where 0 <= i <= deg[0] and 0 <= j <= deg[1].

    For vectors x,y of length n and degrees [xdeg, ydeg], returns a matrix of shape
    (n, (xdeg + 1) * (ydeg + 1)) where each row contains products of Laguerre polynomials.
-/
def lagvander2d {n : Nat} (x y : Vector Float n) (xdeg ydeg : Nat) : 
    Id (Vector (Vector Float ((xdeg + 1) * (ydeg + 1))) n) :=
  do
    return buildResult n xdeg ydeg x y

-- LLM HELPER
lemma fin_mul_add_lt (i : Fin (xdeg + 1)) (j : Fin (ydeg + 1)) : 
  i.val * (ydeg + 1) + j.val < (xdeg + 1) * (ydeg + 1) := by
  have h1 : i.val < xdeg + 1 := i.isLt
  have h2 : j.val < ydeg + 1 := j.isLt
  have h3 : i.val * (ydeg + 1) < (xdeg + 1) * (ydeg + 1) := by
    apply Nat.mul_lt_mul_right
    · simp
    · exact h1
  have h4 : i.val * (ydeg + 1) + j.val < i.val * (ydeg + 1) + (ydeg + 1) := by
    apply Nat.add_lt_add_left h2
  have h5 : i.val * (ydeg + 1) + (ydeg + 1) = (i.val + 1) * (ydeg + 1) := by
    rw [Nat.add_mul]
    simp
  have h6 : (i.val + 1) * (ydeg + 1) ≤ (xdeg + 1) * (ydeg + 1) := by
    apply Nat.mul_le_mul_right
    exact Nat.succ_le_of_lt h1
  rw [h5] at h4
  exact Nat.lt_of_lt_of_le h4 h6

/-- Specification: lagvander2d returns a 2D pseudo-Vandermonde matrix where each row
    contains products of Laguerre polynomials evaluated at corresponding points.

    Precondition: x and y have the same length (enforced by type)
    Postcondition:
    1. The result has shape (n, (xdeg + 1) * (ydeg + 1))
    2. Each element V[k, (ydeg + 1)*i + j] = L_i(x[k]) * L_j(y[k])
    3. The ordering follows the pattern: (0,0), (0,1), ..., (0,ydeg), (1,0), (1,1), ..., (xdeg,ydeg)
    4. For the first column (i=0, j=0), all values are 1 since L_0(x) * L_0(y) = 1
-/
theorem lagvander2d_spec {n : Nat} (x y : Vector Float n) (xdeg ydeg : Nat) :
    ⦃⌜True⌝⦄
    lagvander2d x y xdeg ydeg
    ⦃⇓result => ⌜(∀ k : Fin n, ∀ i : Fin (xdeg + 1), ∀ j : Fin (ydeg + 1),
                    let idx := i.val * (ydeg + 1) + j.val
                    have h_idx : idx < (xdeg + 1) * (ydeg + 1) := fin_mul_add_lt i j
                    (result.get k).get ⟨idx, h_idx⟩ = 
                      laguerrePolynomial i.val (x.get k) * laguerrePolynomial j.val (y.get k))⌝⦄ := by
  simp [lagvander2d, buildResult]
  intro k i j
  simp [Vector.get]
  have h_div : (↑i * (ydeg + 1) + ↑j) / (ydeg + 1) = ↑i := by
    rw [Nat.add_mul_div_left]
    simp [Nat.div_lt_iff_lt_mul]
    exact j.isLt
  have h_mod : (↑i * (ydeg + 1) + ↑j) % (ydeg + 1) = ↑j := by
    rw [Nat.add_mul_mod_self_left]
    simp [Nat.mod_eq_of_lt]
    exact j.isLt
  rw [h_div, h_mod]
  simp