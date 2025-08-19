import Std.Do.Triple
import Std.Tactic.Do
import Batteries.Lean.Float

{
  "name": "numpy.nan_to_num",
  "description": "Replace NaN with zero and infinity with large finite numbers",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nan_to_num.html",
  "doc": "Replace NaN with zero and infinity with large finite numbers (default behaviour) or with the numbers defined by the user using the nan, posinf and/or neginf keywords.",
  "code": "Implemented in numpy/lib/type_check.py"
}
-/

open Std.Do

-- LLM HELPER
def replace_float (x : Float) : Float :=
  if x.isNaN then 0.0
  else if x.isInf && x > 0 then 1.7976931348623157e+308
  else if x.isInf && x < 0 then -1.7976931348623157e+308
  else x

/-- Replace NaN with zero and infinity with large finite numbers element-wise -/
def nan_to_num {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  do
    return x.map replace_float

-- LLM HELPER
def isInf (x : Float) : Bool :=
  x.isInf

-- LLM HELPER
def isFinite (x : Float) : Bool :=
  ¬x.isNaN ∧ ¬x.isInf

-- LLM HELPER
lemma Float.isInf_not_nan {x : Float} (h : x.isInf) : ¬x.isNaN := by
  intro h_nan
  have : ¬(x.isNaN ∧ x.isInf) := by
    simp only [Float.isNaN, Float.isInf]
    intro ⟨h1, h2⟩
    have : x ≠ x := h1
    have : x = Float.inf ∨ x = -Float.inf := by
      cases h2 with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr h
    cases this with
    | inl h => rw [h] at h1; exact h1 rfl
    | inr h => rw [h] at h1; exact h1 rfl
  exact this ⟨h_nan, h⟩

-- LLM HELPER
lemma replace_float_finite (x : Float) : isFinite (replace_float x) := by
  simp [replace_float, isFinite]
  split_ifs with h1 h2 h3
  · simp only [Float.isNaN_zero, Float.isInf_zero, not_false_eq_true, and_self]
  · simp only [Float.isNaN_ofScientific, Float.isInf_ofScientific, not_false_eq_true, and_self]
  · simp only [Float.isNaN_neg, Float.isInf_neg, Float.isNaN_ofScientific, Float.isInf_ofScientific, 
               not_false_eq_true, and_self]
  · constructor
    · exact h1
    · intro h_inf
      cases h2 with
      | inl h => exact h ⟨h_inf, h⟩
      | inr h => 
        have : x.isInf ∧ x < 0 := ⟨h_inf, h⟩
        exact h3 this

/-- Specification: nan_to_num replaces non-finite floating-point values with finite alternatives:
    1. NaN replacement: All NaN values are replaced with 0.0
    2. Positive infinity replacement: All positive infinity values are replaced with a large finite value
    3. Negative infinity replacement: All negative infinity values are replaced with a large negative finite value
    4. Finite value preservation: All finite values remain unchanged
    5. All results are finite: The output contains only finite floating-point numbers -/
theorem nan_to_num_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    nan_to_num x
    ⦃⇓result => ⌜(∀ i : Fin n, 
      let xi := x.get i
      let ri := result.get i
      (xi.isNaN → ri = 0.0) ∧
      (xi.isInf ∧ xi > 0 → ri > 0 ∧ isFinite ri) ∧
      (xi.isInf ∧ xi < 0 → ri < 0 ∧ isFinite ri) ∧
      (isFinite xi → ri = xi)) ∧
    (∀ i : Fin n, isFinite (result.get i))⌝⦄ := by
  intro h
  simp [nan_to_num]
  constructor
  · intro i
    simp [Vector.get_map, replace_float]
    constructor
    · intro h_nan
      simp [if_pos h_nan]
    constructor
    · intro ⟨h_inf, h_pos⟩
      simp [if_neg (Float.isInf_not_nan h_inf), if_pos ⟨h_inf, h_pos⟩]
      constructor
      · norm_num
      · exact replace_float_finite (x.get i)
    constructor
    · intro ⟨h_inf, h_neg⟩
      simp [if_neg (Float.isInf_not_nan h_inf), if_neg (fun h => not_le.mpr h_neg h.le), if_pos ⟨h_inf, h_neg⟩]
      constructor
      · norm_num
      · exact replace_float_finite (x.get i)
    · intro h_finite
      simp [isFinite] at h_finite
      simp [if_neg h_finite.1, if_neg (fun h => h_finite.2 h.1), if_neg (fun h => h_finite.2 h.1)]
  · intro i
    simp [Vector.get_map]
    exact replace_float_finite (x.get i)