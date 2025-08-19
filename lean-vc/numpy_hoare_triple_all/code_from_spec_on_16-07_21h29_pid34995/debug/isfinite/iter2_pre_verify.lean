import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Test element-wise for finiteness (not infinity and not NaN) -/
def isfinite {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  Vector.map (fun f => f.isFinite) x

-- LLM HELPER
lemma float_isFinite_iff_not_special (f : Float) : 
  f.isFinite ↔ (¬f.isInf ∧ ¬f.isNaN) := by
  constructor
  · intro h
    constructor
    · by_contra h_inf
      have : ¬f.isFinite := Float.not_isFinite_of_isInf h_inf
      exact this h
    · by_contra h_nan
      have : ¬f.isFinite := Float.not_isFinite_of_isNaN h_nan
      exact this h
  · intro ⟨h_not_inf, h_not_nan⟩
    by_contra h_not_finite
    cases' Float.not_isFinite_iff.mp h_not_finite with h_nan h_inf
    · exact h_not_nan h_nan
    · exact h_not_inf h_inf

-- LLM HELPER
lemma float_not_isFinite_iff_special (f : Float) : 
  ¬f.isFinite ↔ (f.isNaN ∨ f.isInf) := by
  rw [float_isFinite_iff_not_special]
  simp [not_and_or]

-- LLM HELPER
lemma zero_isFinite : (0.0 : Float).isFinite := by
  rw [float_isFinite_iff_not_special]
  constructor
  · exact Float.zero_not_isInf
  · exact Float.zero_not_isNaN

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
  have : ¬(x + y).isFinite := Float.not_isFinite_of_isNaN h_nan
  sorry

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
  simp only [Vector.map, Vector.get_mk]
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