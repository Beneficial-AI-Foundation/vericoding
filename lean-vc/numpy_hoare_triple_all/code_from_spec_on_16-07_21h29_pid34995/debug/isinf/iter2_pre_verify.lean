import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Test element-wise for positive or negative infinity in a vector -/
def isinf {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  return Vector.ofFn (fun i => (x.get i).isInf)

-- LLM HELPER
lemma float_isInf_not_isNaN (f : Float) : f.isInf → ¬f.isNaN := by
  intro h
  simp [Float.isInf, Float.isNaN] at h ⊢
  exact h

-- LLM HELPER
lemma float_isInf_not_isFinite (f : Float) : f.isInf → ¬f.isFinite := by
  intro h
  simp [Float.isInf, Float.isFinite] at h ⊢
  exact h

-- LLM HELPER
lemma float_zero_not_isInf (f : Float) : f = 0.0 → ¬f.isInf := by
  intro h
  simp [Float.isInf] at ⊢
  rw [h]
  simp [Float.isInf]

/-- Specification: isinf returns true for positive or negative infinity, false otherwise.
    
    This function tests each element according to IEEE 754 floating-point standard:
    - Returns true if the element is positive infinity or negative infinity
    - Returns false for all other values including NaN, finite numbers, and zero
    
    Mathematical properties:
    1. Infinity detection: result[i] = true iff x[i] is infinite
    2. Distinction from NaN: infinity and NaN are mutually exclusive
    3. Result preserves shape: output vector has same length as input
    4. Finite values: All normal, subnormal, and zero values return false
    5. Specific infinities: Both positive and negative infinity are correctly identified
-/
theorem isinf_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isinf x
    ⦃⇓result => ⌜∀ i : Fin n, 
      (result.get i = (x.get i).isInf) ∧
      (¬(x.get i).isInf → result.get i = false) ∧
      ((x.get i).isNaN → result.get i = false) ∧
      (x.get i = 0.0 → result.get i = false) ∧
      (result.get i = true → ¬(x.get i).isFinite) ∧
      (result.get i = true → ¬(x.get i).isNaN)⌝⦄ := by
  unfold isinf
  simp [wpReturn]
  intro i
  simp [Vector.get, Vector.ofFn]
  intro h
  simp [h]
  constructor
  · rfl
  constructor
  · intro h_not_inf
    simp [h_not_inf]
  constructor
  · intro h_nan
    by_cases h_inf : (x.get i).isInf
    · simp [h_inf]
      exact float_isInf_not_isNaN (x.get i) h_inf h_nan
    · simp [h_inf]
  constructor
  · intro h_zero
    simp [float_zero_not_isInf (x.get i) h_zero]
  constructor
  · intro h_true
    exact float_isInf_not_isFinite (x.get i) h_true
  · intro h_true
    exact float_isInf_not_isNaN (x.get i) h_true