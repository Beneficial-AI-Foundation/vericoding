import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Test element-wise for finiteness (not infinity and not NaN) -/
def isfinite {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  pure (Vector.map (fun f => f.isFinite) x)

-- LLM HELPER
lemma float_isFinite_iff_not_special (f : Float) : 
  f.isFinite ↔ (¬f.isInf ∧ ¬f.isNaN) := by
  constructor
  · intro h
    constructor
    · by_contra h_inf
      simp [Float.isFinite] at h
      simp [Float.isInf] at h_inf
      contradiction
    · by_contra h_nan
      simp [Float.isFinite] at h
      simp [Float.isNaN] at h_nan
      contradiction
  · intro ⟨h_not_inf, h_not_nan⟩
    simp [Float.isFinite]
    constructor
    · exact h_not_nan
    · exact h_not_inf

-- LLM HELPER
lemma float_not_isFinite_iff_special (f : Float) : 
  ¬f.isFinite ↔ (f.isNaN ∨ f.isInf) := by
  rw [float_isFinite_iff_not_special]
  simp [not_and_or]

-- LLM HELPER
lemma zero_isFinite : (0.0 : Float).isFinite := by
  rw [float_isFinite_iff_not_special]
  constructor
  · simp [Float.isInf]
  · simp [Float.isNaN]

-- LLM HELPER
lemma isFinite_bounded (f : Float) : 
  f.isFinite → ∃ (bound : Float), Float.abs f ≤ bound := by
  intro h
  use Float.abs f
  rfl

-- LLM HELPER
lemma finite_add_finite_not_nan (x y : Float) : 
  x.isFinite → y.isFinite → ¬(x + y).isNaN := by
  intro hx hy
  by_contra h_nan
  simp [Float.isFinite, Float.isNaN] at *
  cases hx with
  | mk h1 h2 => 
    cases hy with
    | mk h3 h4 => 
      contradiction

/-- Specification: isfinite returns true for finite values, false for infinity and NaN -/
theorem isfinite_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isfinite x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 
      (¬(x.get i).isInf ∧ ¬(x.get i).isNaN) ∧
      -- Core mathematical property: equivalence with isFinite
      (result.get i = true ↔ (x.get i).isFinite) ∧
      -- Inverse property: false iff NaN or infinity
      (result.get i = false ↔ ((x.get i).isNaN ∨ (x.get i).isInf)) ∧
      -- Specific cases: zero and normal numbers are finite
      (x.get i = 0.0 → result.get i = true) ∧
      -- Mathematical property: finite numbers have bounded absolute value
      (result.get i = true → ∃ (bound : Float), Float.abs (x.get i) ≤ bound) ∧
      -- Consistency: if not finite, then either NaN or infinity
      (result.get i = false → ((x.get i).isNaN ∨ (x.get i).isInf)) ∧
      -- Arithmetic stability: finite + finite arithmetic operations
      (result.get i = true → ∀ (y : Float), y.isFinite → 
        ((x.get i + y).isFinite ∨ (x.get i + y).isInf)) ∧
      -- IEEE 754 compliance: finite values exclude special values
      (result.get i = true → ¬(x.get i).isNaN ∧ ¬(x.get i).isInf)⌝⦄ := by
  unfold isfinite
  simp only [pure, Vector.map, Vector.get_mk]
  intro i
  simp only [List.get_map, Bool.eq_true_iff]
  constructor
  · rw [float_isFinite_iff_not_special]
    rfl
  constructor
  · rfl
  constructor
  · rw [←Bool.not_eq_true_iff_eq_false]
    rw [float_not_isFinite_iff_special]
    rfl
  constructor
  · intro h
    rw [h]
    exact zero_isFinite
  constructor
  · intro h
    exact isFinite_bounded (x.get i) h
  constructor
  · intro h
    rw [←Bool.not_eq_true_iff_eq_false] at h
    rw [float_not_isFinite_iff_special] at h
    exact h
  constructor
  · intro h y hy
    by_cases hsum : (x.get i + y).isFinite
    · left; exact hsum
    · right; rw [float_not_isFinite_iff_special] at hsum
      cases' hsum with hnan hinf
      · exfalso
        exact finite_add_finite_not_nan (x.get i) y h hy hnan
      · exact hinf
  · intro h
    rw [float_isFinite_iff_not_special] at h
    exact h