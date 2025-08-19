import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def float_isclose_element (a b : Float) (rtol : Float) (atol : Float) (equal_nan : Bool) : Bool :=
  if a.isNaN ∧ b.isNaN then
    equal_nan
  else if ¬Float.isFinite a ∨ ¬Float.isFinite b then
    a = b
  else
    Float.abs (a - b) ≤ atol + rtol * Float.abs b

/-- Returns a boolean array where two arrays are element-wise equal within a tolerance.
    For finite values, isclose uses the equation: absolute(a - b) <= (atol + rtol * absolute(b))
    where `b` is treated as the reference value. -/
def isclose {n : Nat} (a b : Vector Float n) (rtol : Float) (atol : Float) (equal_nan : Bool) : Id (Vector Bool n) :=
  Vector.ofFn (fun i => float_isclose_element (a.get i) (b.get i) rtol atol equal_nan)

-- LLM HELPER
lemma float_isclose_element_spec (a b : Float) (rtol : Float) (atol : Float) (equal_nan : Bool) :
  let result := float_isclose_element a b rtol atol equal_nan
  -- Core tolerance check for finite values
  (Float.isFinite a ∧ Float.isFinite b → 
   (result = true ↔ Float.abs (a - b) ≤ atol + rtol * Float.abs b)) ∧
  -- Infinite values are equal if they match exactly
  (¬Float.isFinite a ∨ ¬Float.isFinite b → 
   (result = true ↔ a = b)) ∧
  -- NaN handling depends on equal_nan parameter
  (a.isNaN ∧ b.isNaN → 
   (result = true ↔ equal_nan = true)) ∧
  -- Asymmetric property: uses b as reference value
  (result = false ↔ 
   (Float.isFinite a ∧ Float.isFinite b ∧ 
    Float.abs (a - b) > atol + rtol * Float.abs b) ∨
   (¬Float.isFinite a ∨ ¬Float.isFinite b) ∧ a ≠ b ∨
   (a.isNaN ∧ b.isNaN ∧ equal_nan = false)) := by
  simp [float_isclose_element]
  constructor
  · intro h_finite
    simp [h_finite.1.isNaN_eq_false, h_finite.2.isNaN_eq_false]
    simp [Float.isFinite] at h_finite
    simp [h_finite]
  constructor
  · intro h_not_finite
    simp [Float.isFinite] at h_not_finite
    cases' h_not_finite with h h
    · simp [h]
    · simp [h]
  constructor
  · intro h_nan
    simp [h_nan.1, h_nan.2]
  · simp
    tauto

/-- Specification: isclose returns a boolean array indicating element-wise closeness within tolerance -/
theorem isclose_spec {n : Nat} (a b : Vector Float n) (rtol : Float) (atol : Float) (equal_nan : Bool) 
    (h_rtol_nonneg : rtol ≥ 0) (h_atol_nonneg : atol ≥ 0) :
    ⦃⌜rtol ≥ 0 ∧ atol ≥ 0⌝⦄
    isclose a b rtol atol equal_nan
    ⦃⇓result => ⌜∀ i : Fin n, 
        -- Core tolerance check for finite values
        (Float.isFinite (a.get i) ∧ Float.isFinite (b.get i) → 
         (result.get i = true ↔ 
          Float.abs (a.get i - b.get i) ≤ atol + rtol * Float.abs (b.get i))) ∧
        -- Infinite values are equal if they match exactly
        (¬Float.isFinite (a.get i) ∨ ¬Float.isFinite (b.get i) → 
         (result.get i = true ↔ a.get i = b.get i)) ∧
        -- NaN handling depends on equal_nan parameter
        ((a.get i).isNaN ∧ (b.get i).isNaN → 
         (result.get i = true ↔ equal_nan = true)) ∧
        -- Asymmetric property: uses b as reference value
        (result.get i = false ↔ 
         (Float.isFinite (a.get i) ∧ Float.isFinite (b.get i) ∧ 
          Float.abs (a.get i - b.get i) > atol + rtol * Float.abs (b.get i)) ∨
         (¬Float.isFinite (a.get i) ∨ ¬Float.isFinite (b.get i)) ∧ a.get i ≠ b.get i ∨
         ((a.get i).isNaN ∧ (b.get i).isNaN ∧ equal_nan = false))⌝⦄ := by
  apply triple_spec_intro
  intro h_pre
  simp [isclose]
  intro i
  simp [Vector.get_ofFn]
  exact float_isclose_element_spec (a.get i) (b.get i) rtol atol equal_nan