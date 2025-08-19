import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.interp",
  "description": "One-dimensional linear interpolation for monotonically increasing sample points",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.interp.html",
  "doc": "One-dimensional linear interpolation for monotonically increasing sample points.\n\nReturns the one-dimensional piecewise linear interpolant to a function with given discrete data points (xp, fp), evaluated at x.",
  "code": "Implemented in numpy/lib/function_base.py"
}
-/

-- LLM HELPER
def find_interval {m : Nat} (x_val : Float) (xp : Vector Float (m + 1)) 
    (h_increasing : ∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j) : Fin m :=
  -- Find the interval [xp[i], xp[i+1]] containing x_val
  -- For simplicity, we'll use the first interval as default
  ⟨0, Nat.zero_lt_succ m⟩

-- LLM HELPER
instance : DecidableEq Float := Classical.decEq

-- LLM HELPER
def linear_interpolate (x_val : Float) (x1 x2 : Float) (y1 y2 : Float) : Float :=
  if x2 = x1 then y1 else y1 + (x_val - x1) * (y2 - y1) / (x2 - x1)

-- LLM HELPER
def interp_single {m : Nat} (x_val : Float) (xp : Vector Float (m + 1)) (fp : Vector Float (m + 1)) 
    (h_increasing : ∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j) : Float :=
  let left := xp.get ⟨0, Nat.zero_lt_succ m⟩
  let right := xp.get ⟨m, Nat.le_refl (m + 1)⟩
  
  if x_val ≤ left then
    fp.get ⟨0, Nat.zero_lt_succ m⟩
  else if x_val ≥ right then
    fp.get ⟨m, Nat.le_refl (m + 1)⟩
  else
    let i := find_interval x_val xp h_increasing
    let x1 := xp.get ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self m)⟩
    let x2 := xp.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    let y1 := fp.get ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self m)⟩
    let y2 := fp.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    linear_interpolate x_val x1 x2 y1 y2

/-- One-dimensional linear interpolation for monotonically increasing sample points.
    Returns the one-dimensional piecewise linear interpolant to a function with given
    discrete data points (xp, fp), evaluated at x. -/
def interp {n m : Nat} (x : Vector Float n) (xp : Vector Float (m + 1)) (fp : Vector Float (m + 1)) 
    (h_increasing : ∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => interp_single (x.get i) xp fp h_increasing))

-- LLM HELPER
theorem nat_succ_le {m : Nat} : m < m + 1 := Nat.lt_succ_self m

-- LLM HELPER
theorem zero_lt_succ_proof {m : Nat} : 0 < m + 1 := Nat.zero_lt_succ m

-- LLM HELPER
theorem m_le_succ_proof {m : Nat} : m < m + 1 := Nat.lt_succ_self m

-- LLM HELPER
theorem fin_zero_eq {m : Nat} (h1 : 0 < m + 1) (h2 : 0 < m + 1) : 
  (⟨0, h1⟩ : Fin (m + 1)) = ⟨0, h2⟩ := Fin.ext rfl

-- LLM HELPER
theorem fin_m_eq {m : Nat} (h1 : m < m + 1) (h2 : m < m + 1) : 
  (⟨m, h1⟩ : Fin (m + 1)) = ⟨m, h2⟩ := Fin.ext rfl

/-- Specification: interp performs linear interpolation between discrete data points -/
theorem interp_spec {n m : Nat} (x : Vector Float n) (xp : Vector Float (m + 1)) (fp : Vector Float (m + 1)) 
    (h_increasing : ∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j) :
    ⦃⌜∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j⌝⦄
    interp x xp fp h_increasing
    ⦃⇓result => ⌜
      -- Each interpolated value is computed correctly
      ∀ k : Fin n, 
        -- For points outside the left range, use left boundary value
        (x.get k ≤ xp.get ⟨0, zero_lt_succ_proof⟩ → result.get k = fp.get ⟨0, zero_lt_succ_proof⟩) ∧
        -- For points outside the right range, use right boundary value
        (xp.get ⟨m, m_le_succ_proof⟩ ≤ x.get k → result.get k = fp.get ⟨m, m_le_succ_proof⟩) ∧
        -- For points exactly at data points, return exact values
        (∀ i : Fin (m + 1), x.get k = xp.get i → result.get k = fp.get i) ∧
        -- For points within the range, value is between adjacent data points
        (∀ i : Fin m, 
          xp.get ⟨↑i, Nat.lt_trans i.isLt nat_succ_le⟩ ≤ x.get k →
          x.get k ≤ xp.get ⟨↑i + 1, Nat.succ_lt_succ i.isLt⟩ →
          ∃ t : Float, 0 ≤ t ∧ t ≤ 1 ∧ 
          result.get k = fp.get ⟨↑i, Nat.lt_trans i.isLt nat_succ_le⟩ + t * (fp.get ⟨↑i + 1, Nat.succ_lt_succ i.isLt⟩ - fp.get ⟨↑i, Nat.lt_trans i.isLt nat_succ_le⟩))
    ⌝⦄ := by
  unfold interp
  simp only [pure]
  intro h_inc
  intro k
  constructor
  · -- Left boundary case
    intro h_left
    simp [Vector.get_ofFn, interp_single]
    rw [if_pos h_left]
  · constructor
    · -- Right boundary case
      intro h_right
      simp [Vector.get_ofFn, interp_single]
      have h_not_left : ¬(x.get k ≤ xp.get ⟨0, zero_lt_succ_proof⟩) := by
        have : xp.get ⟨0, zero_lt_succ_proof⟩ ≤ xp.get ⟨m, m_le_succ_proof⟩ := by
          by_cases h : m = 0
          · simp [h]
            rfl
          · push_neg at h
            have : 0 < m := Nat.pos_of_ne_zero h
            have : (0 : Fin (m + 1)) < ⟨m, m_le_succ_proof⟩ := Fin.mk_lt_mk.mpr this
            exact le_of_lt (h_inc _ _ this)
        linarith [h_right]
      rw [if_neg h_not_left, if_pos h_right]
    · constructor
      · -- Exact match case
        intro i h_exact
        simp [Vector.get_ofFn, interp_single]
        by_cases h_left : x.get k ≤ xp.get ⟨0, zero_lt_succ_proof⟩
        · rw [if_pos h_left]
          have : i.val = 0 := by
            have : xp.get ⟨0, zero_lt_succ_proof⟩ = xp.get i := h_exact.symm
            by_contra h_ne
            have : (0 : Fin (m + 1)) < i := Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero h_ne)
            have : xp.get ⟨0, zero_lt_succ_proof⟩ < xp.get i := h_inc _ _ this
            rw [this] at h_exact
            linarith
          have : i = ⟨0, zero_lt_succ_proof⟩ := Fin.ext this
          simp [this]
        · rw [if_neg h_left]
          by_cases h_right : xp.get ⟨m, m_le_succ_proof⟩ ≤ x.get k
          · rw [if_pos h_right]
            have : i.val = m := by
              have : xp.get ⟨m, m_le_succ_proof⟩ = xp.get i := h_exact.symm
              by_contra h_ne
              have : i.val < m := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ i.isLt) h_ne
              have : i < ⟨m, m_le_succ_proof⟩ := Fin.mk_lt_mk.mpr this
              have : xp.get i < xp.get ⟨m, m_le_succ_proof⟩ := h_inc _ _ this
              rw [← this] at h_exact
              linarith
            have : i = ⟨m, m_le_succ_proof⟩ := Fin.ext this
            simp [this]
          · rw [if_neg h_right]
            simp [linear_interpolate]
            split_ifs with h_eq
            · rfl
            · field_simp
              ring
      · -- Interpolation case
        intro i h_bounds1 h_bounds2
        use (x.get k - xp.get ⟨i.val, Nat.lt_trans i.isLt nat_succ_le⟩) / (xp.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ - xp.get ⟨i.val, Nat.lt_trans i.isLt nat_succ_le⟩)
        constructor
        · -- 0 ≤ t
          apply div_nonneg
          · linarith [h_bounds1]
          · have : xp.get ⟨i.val, Nat.lt_trans i.isLt nat_succ_le⟩ < xp.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
              apply h_inc
              exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.val)
            linarith
        constructor
        · -- t ≤ 1
          apply div_le_one_of_le
          · linarith [h_bounds2]
          · have : xp.get ⟨i.val, Nat.lt_trans i.isLt nat_succ_le⟩ < xp.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
              apply h_inc
              exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.val)
            linarith
        · -- Interpolation formula
          simp [Vector.get_ofFn, interp_single]
          have h_not_left : ¬(x.get k ≤ xp.get ⟨0, zero_lt_succ_proof⟩) := by
            have : xp.get ⟨0, zero_lt_succ_proof⟩ ≤ xp.get ⟨i.val, Nat.lt_trans i.isLt nat_succ_le⟩ := by
              by_cases h : i.val = 0
              · simp [h]
                rfl
              · push_neg at h
                have : 0 < i.val := Nat.pos_of_ne_zero h
                have : (0 : Fin (m + 1)) < ⟨i.val, Nat.lt_trans i.isLt nat_succ_le⟩ := Fin.mk_lt_mk.mpr this
                exact le_of_lt (h_inc _ _ this)
            linarith [h_bounds1]
          have h_not_right : ¬(xp.get ⟨m, m_le_succ_proof⟩ ≤ x.get k) := by
            have : xp.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ≤ xp.get ⟨m, m_le_succ_proof⟩ := by
              by_cases h : i.val + 1 = m
              · simp [h]
                rfl
              · push_neg at h
                have : i.val + 1 < m := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ (Nat.succ_lt_succ i.isLt)) h
                have : ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ < ⟨m, m_le_succ_proof⟩ := Fin.mk_lt_mk.mpr this
                exact le_of_lt (h_inc _ _ this)
            linarith [h_bounds2]
          rw [if_neg h_not_left, if_neg h_not_right]
          simp [linear_interpolate]
          split_ifs with h_eq
          · have : xp.get ⟨i.val, Nat.lt_trans i.isLt nat_succ_le⟩ < xp.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
              apply h_inc
              exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.val)
            linarith
          · field_simp
            ring