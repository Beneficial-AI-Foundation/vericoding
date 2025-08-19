import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermemulx_aux {n : Nat} (c : Vector Float n) : Vector Float (n + 1) :=
  if n = 0 then 
    Vector.replicate 1 0.0
  else
    let result := Vector.replicate (n + 1) 0.0
    let result := result.set ⟨0, by simp [Nat.zero_lt_succ]⟩ 0.0
    let result := if n > 0 then
      result.set ⟨1, by simp [Nat.succ_lt_succ, Nat.zero_lt_succ]⟩ (c.get ⟨0, by simp; omega⟩)
    else result
    let rec loop (i : Nat) (acc : Vector Float (n + 1)) : Vector Float (n + 1) :=
      if h : i < n then
        let acc := acc.set ⟨i + 1, by simp [Nat.succ_lt_succ]; exact Nat.lt_succ_of_lt h⟩ (c.get ⟨i, h⟩)
        if h' : i > 0 then
          let old_val := acc.get ⟨i - 1, by omega⟩
          let acc := acc.set ⟨i - 1, by omega⟩ (old_val + c.get ⟨i, h⟩ * i.toFloat)
          loop (i + 1) acc
        else
          loop (i + 1) acc
      else acc
    loop 1 result

/-- Multiply a Hermite series by x using the recursion relationship for Hermite polynomials. -/
def hermemulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  pure (hermemulx_aux c)

-- LLM HELPER
lemma nat_pred_lt_succ_helper {n : Nat} (h : n > 0) : 0 < n := h

-- LLM HELPER 
lemma nat_pred_lt_helper {n : Nat} (h : n > 1) : 1 < n := h

/-- Specification: hermemulx multiplies a Hermite series by x using the recursion relationship.
    The result has one more coefficient than the input, implementing the transformation
    based on the Hermite polynomial recursion: xP_i(x) = (P_{i + 1}(x) + iP_{i - 1}(x)) -/
theorem hermemulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    hermemulx c
    ⦃⇓result => ⌜
      -- Coefficient at position 0 is always 0 (no constant term in x*polynomial)
      result.get ⟨0, by simp [Nat.zero_lt_succ]⟩ = 0 ∧
      -- For n > 0: coefficient at position 1 comes from c[0] plus recursive contributions  
      (∀ (h : n > 0), result.get ⟨1, by simp [Nat.succ_lt_succ, Nat.zero_lt_succ]⟩ = c.get ⟨0, nat_pred_lt_succ_helper h⟩ + 
        (if n > 1 then (c.get ⟨1, nat_pred_lt_helper (by omega)⟩) * (1 : Float) else 0)) ∧
      -- For i ≥ 1: result[i+1] gets c[i] (coefficient shift up)
      (∀ i : Fin n, i.val ≥ 1 → result.get ⟨i.val + 1, by simp [Nat.succ_lt_succ]; exact Nat.lt_succ_of_lt i.isLt⟩ = c.get i)
    ⌝⦄ := by
  unfold hermemulx
  simp only [Id.pure_bind]
  simp only [True_implies_iff]
  unfold hermemulx_aux
  split
  · case h_1 h =>
    simp [h]
    constructor
    · simp [Vector.get, Vector.replicate]
    constructor
    · intro h_pos
      simp [h] at h_pos
    · intro i h_ge
      simp [h] at i
      exact i.elim
  · case h_2 h =>
    simp
    constructor
    · simp [Vector.get, Vector.set, Vector.replicate]
    constructor
    · intro h_pos
      simp [Vector.get, Vector.set, Vector.replicate]
      omega
    · intro i h_ge
      simp [Vector.get, Vector.set, Vector.replicate]
      omega