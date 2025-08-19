import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Helper definition for Chebyshev polynomial of the first kind T_n(x).
    This is a placeholder - the actual implementation would use the proper
    recursive definition or closed form.
-/
def chebyshevT (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | n + 2 => 2.0 * x * chebyshevT (n + 1) x - chebyshevT n x

/-- numpy.polynomial.chebyshev.chebvander2d: Pseudo-Vandermonde matrix of given degrees.

    Returns the pseudo-Vandermonde matrix of degrees `deg` and sample
    points `(x, y)`. The pseudo-Vandermonde matrix is defined by

    V[..., (deg[1] + 1)*i + j] = T_i(x) * T_j(y),

    where `0 <= i <= deg[0]` and `0 <= j <= deg[1]`. The leading indices of
    `V` index the points `(x, y)` and the last index encodes the degrees of
    the Chebyshev polynomials.

    This function creates a matrix useful for least squares fitting and
    evaluation of 2-D Chebyshev series.
-/
def chebvander2d {n : Nat} (x y : Vector Float n) (xdeg ydeg : Nat) : 
    Id (Vector (Vector Float ((xdeg + 1) * (ydeg + 1))) n) :=
  pure (Vector.map (fun k => 
    Vector.mapIdx (fun idx _ => 
      let i := idx / (ydeg + 1)
      let j := idx % (ydeg + 1)
      (chebyshevT i (x.get k)) * (chebyshevT j (y.get k))
    ) (Vector.replicate ((xdeg + 1) * (ydeg + 1)) 0.0)
  ) (Vector.ofFn (fun i => i)))

-- LLM HELPER
lemma div_mod_decomp (idx : Fin ((xdeg + 1) * (ydeg + 1))) (xdeg ydeg : Nat) :
    idx.val = (idx.val / (ydeg + 1)) * (ydeg + 1) + (idx.val % (ydeg + 1)) := by
  rw [Nat.div_add_mod]

-- LLM HELPER
lemma div_lt_xdeg_plus_one (idx : Fin ((xdeg + 1) * (ydeg + 1))) (xdeg ydeg : Nat) :
    idx.val / (ydeg + 1) < xdeg + 1 := by
  have h : ydeg + 1 > 0 := Nat.succ_pos ydeg
  exact Nat.div_lt_iff_lt_mul h |>.mpr idx.isLt

-- LLM HELPER
lemma mod_lt_ydeg_plus_one (idx : Fin ((xdeg + 1) * (ydeg + 1))) (xdeg ydeg : Nat) :
    idx.val % (ydeg + 1) < ydeg + 1 := by
  exact Nat.mod_lt idx.val (Nat.succ_pos ydeg)

-- LLM HELPER
lemma idx_eq_formula (i : Fin (xdeg + 1)) (j : Fin (ydeg + 1)) :
    i.val * (ydeg + 1) + j.val = i.val * (ydeg + 1) + j.val := by
  rfl

-- LLM HELPER
lemma Vector.get_map {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
    (Vector.map f v).get i = f (v.get i) := by
  rfl

-- LLM HELPER
lemma Vector.get_mapIdx {α β : Type*} {n : Nat} (f : Fin n → α → β) (v : Vector α n) (i : Fin n) :
    (Vector.mapIdx f v).get i = f i (v.get i) := by
  rfl

-- LLM HELPER
lemma Vector.get_replicate {α : Type*} {n : Nat} (x : α) (i : Fin n) :
    (Vector.replicate n x).get i = x := by
  rfl

-- LLM HELPER
lemma add_mod_mul_div_cancel (j : Fin (ydeg + 1)) (i : Nat) (h : ydeg + 1 > 0) :
    (i * (ydeg + 1) + j.val) % (ydeg + 1) = j.val := by
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt j.isLt

-- LLM HELPER
lemma add_mod_mul_div_left (j : Fin (ydeg + 1)) (i : Nat) (h : ydeg + 1 > 0) :
    (i * (ydeg + 1) + j.val) / (ydeg + 1) = i := by
  rw [Nat.add_mul_div_left _ _ h]
  rw [Nat.div_eq_zero_iff_lt]
  exact j.isLt

-- LLM HELPER
lemma mul_lt_mul_of_pos_right_and_lt {a b c : Nat} (h1 : a < b) (h2 : c > 0) :
    a * c < b * c := by
  exact Nat.mul_lt_mul_right h2 h1

-- LLM HELPER
lemma add_lt_of_lt_sub_simpl {a b c : Nat} (h1 : a < b) (h2 : c * b < d) :
    c * b + a < d := by
  omega

/-- Specification: chebvander2d returns a matrix where each row corresponds to
    a point (x[k], y[k]) and contains the products of Chebyshev polynomials
    T_i(x[k]) * T_j(y[k]) for all combinations of i and j.

    Precondition: True (no special preconditions)
    Postcondition: 
    - The result has n rows (one for each point)
    - Each row has (xdeg + 1) * (ydeg + 1) elements
    - For each point k and degrees (i, j), the element at position 
      (ydeg + 1) * i + j equals T_i(x[k]) * T_j(y[k])
    - The elements are ordered column-major: varying j (y-degree) fastest
-/
theorem chebvander2d_spec {n : Nat} (x y : Vector Float n) (xdeg ydeg : Nat) :
    ⦃⌜True⌝⦄
    chebvander2d x y xdeg ydeg
    ⦃⇓result => ⌜∀ (k : Fin n) (i : Fin (xdeg + 1)) (j : Fin (ydeg + 1)),
                  let idx := i.val * (ydeg + 1) + j.val
                  (result.get k).get ⟨idx, by 
                    have h1 : i.val < xdeg + 1 := i.isLt
                    have h2 : j.val < ydeg + 1 := j.isLt
                    have h3 : i.val * (ydeg + 1) < (xdeg + 1) * (ydeg + 1) := by
                      exact mul_lt_mul_of_pos_right_and_lt h1 (Nat.succ_pos ydeg)
                    have h4 : idx < (xdeg + 1) * (ydeg + 1) := by
                      simp [idx]
                      exact add_lt_of_lt_sub_simpl h2 h3
                    exact h4⟩ = 
                  (chebyshevT i.val (x.get k)) * (chebyshevT j.val (y.get k))⌝⦄ := by
  simp [chebvander2d]
  intro k i j
  rw [Vector.get_map, Vector.get_mapIdx, Vector.get_replicate]
  have h_div : (i.val * (ydeg + 1) + j.val) / (ydeg + 1) = i.val := by
    exact add_mod_mul_div_left j i.val (Nat.succ_pos ydeg)
  have h_mod : (i.val * (ydeg + 1) + j.val) % (ydeg + 1) = j.val := by
    exact add_mod_mul_div_cancel j i.val (Nat.succ_pos ydeg)
  rw [h_div, h_mod]
  rfl