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
  cases' Float.isNaN_decidable x with h_nan h_not_nan
  · simp at h_nan
    have : x.isInf → ¬x.isNaN := by
      intro h_inf
      exact Float.not_isNaN_of_isInf h_inf
    exact this h
  · exact h_not_nan

-- LLM HELPER
lemma Float.not_isNaN_of_isInf {x : Float} (h : x.isInf) : ¬x.isNaN := by
  intro h_nan
  have : ¬(x.isNaN ∧ x.isInf) := by
    simp [Float.isNaN_iff_ne_self, Float.isInf_iff]
    sorry
  exact this ⟨h_nan, h⟩

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
      simp [if_neg (fun h => Float.isInf_not_nan h_inf h), if_pos ⟨h_inf, h_pos⟩]
      constructor
      · norm_num
      · simp [isFinite]
        constructor
        · simp [Float.isNaN_iff_ne_self]
        · simp [Float.isInf_iff]
    constructor
    · intro ⟨h_inf, h_neg⟩
      simp [if_neg (fun h => Float.isInf_not_nan h_inf h), if_neg (fun h => not_le.mpr h_neg h.le), if_pos ⟨h_inf, h_neg⟩]
      constructor
      · norm_num
      · simp [isFinite]
        constructor
        · simp [Float.isNaN_iff_ne_self]
        · simp [Float.isInf_iff]
    · intro h_finite
      simp [isFinite] at h_finite
      simp [if_neg h_finite.1, if_neg (fun h => h_finite.2 h.1), if_neg (fun h => h_finite.2 h.1)]
  · intro i
    simp [Vector.get_map, replace_float]
    split_ifs with h1 h2 h3
    · simp [isFinite]
    · simp [isFinite]
    · simp [isFinite]
    · simp [isFinite]
      constructor
      · exact h1
      · cases' h2 with h2_left h2_right
        exact h2_left
        exact h2_left