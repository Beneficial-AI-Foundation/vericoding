import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermemulx_aux {n : Nat} (c : Vector Float n) : Vector Float (n + 1) :=
  if n = 0 then 
    Vector.replicate 1 0
  else
    let result := Vector.replicate (n + 1) 0
    let result := result.set ⟨0, by simp [Nat.zero_lt_succ]⟩ 0
    let result := if n > 0 then
      result.set ⟨1, by simp [Nat.succ_lt_succ, Nat.zero_lt_succ]⟩ (c.get ⟨0, by simp [Nat.pos_iff_ne_zero.mp (Nat.pos_of_ne_zero (ne_of_gt (by assumption)))]⟩)
    else result
    let rec loop (i : Nat) (acc : Vector Float (n + 1)) : Vector Float (n + 1) :=
      if h : i < n then
        let acc := acc.set ⟨i + 1, by simp [Nat.succ_lt_succ]; exact Nat.lt_succ_of_lt h⟩ (c.get ⟨i, h⟩)
        if h' : i > 0 then
          let old_val := acc.get ⟨i - 1, by
            have : i - 1 < n + 1 := by
              cases' i with i'
              · simp at h'
              · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
                exact Nat.lt_succ_of_lt h
          ⟩
          let acc := acc.set ⟨i - 1, by
            have : i - 1 < n + 1 := by
              cases' i with i'
              · simp at h'
              · simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
                exact Nat.lt_succ_of_lt h
          ⟩ (old_val + c.get ⟨i, h⟩ * i.toFloat)
          loop (i + 1) acc
        else
          loop (i + 1) acc
      else acc
    loop 1 result

/-- Multiply a Hermite series by x using the recursion relationship for Hermite polynomials. -/
def hermemulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  pure (hermemulx_aux c)

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
      (∀ (h : n > 0), result.get ⟨1, by simp [Nat.succ_lt_succ, Nat.zero_lt_succ]⟩ = c.get ⟨0, h⟩ + 
        (if n > 1 then (c.get ⟨1, Nat.succ_lt_succ (Nat.zero_lt_of_ne_zero (Nat.ne_of_gt (Nat.pred_lt_iff.mp (by simp [Nat.pred_succ]; exact Nat.zero_lt_of_ne_zero (ne_of_gt h)))))⟩) * (1 : Float) else 0)) ∧
      -- For i ≥ 1: result[i+1] gets c[i] (coefficient shift up)
      (∀ i : Fin n, i.val ≥ 1 → result.get ⟨i.val + 1, by simp [Nat.succ_lt_succ]; exact Nat.lt_succ_of_lt i.isLt⟩ = c.get i)
    ⌝⦄ := by
  unfold hermemulx
  simp only [pure_bind, pure_return, returnSpec]
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
      cases' n with n'
      · simp at h_pos
      · simp
    · intro i h_ge
      simp [Vector.get, Vector.set, Vector.replicate]
      cases' n with n'
      · simp at i
        exact i.elim
      · simp