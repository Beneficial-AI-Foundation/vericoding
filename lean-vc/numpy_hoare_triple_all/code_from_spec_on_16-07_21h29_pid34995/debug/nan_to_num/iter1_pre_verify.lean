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
  else if x = Float.inf then 1.7976931348623157e+308
  else if x = -Float.inf then -1.7976931348623157e+308
  else x

/-- Replace NaN with zero and infinity with large finite numbers element-wise -/
def nan_to_num {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  do
    return x.map replace_float

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
      (xi = Float.inf → ri > 0 ∧ ri.isFinite) ∧
      (xi = -Float.inf → ri < 0 ∧ ri.isFinite) ∧
      (xi.isFinite → ri = xi)) ∧
    (∀ i : Fin n, (result.get i).isFinite)⌝⦄ := by
  intro h
  simp [nan_to_num]
  constructor
  · intro i
    simp [Vector.get_map, replace_float]
    constructor
    · intro h_nan
      simp [if_pos h_nan]
    constructor
    · intro h_inf
      simp [if_neg (Float.inf_not_nan), if_pos h_inf]
      constructor
      · norm_num
      · simp [Float.isFinite]
    constructor
    · intro h_neg_inf
      simp [if_neg (Float.neg_inf_not_nan), if_neg (Float.neg_inf_ne_inf), if_pos h_neg_inf]
      constructor
      · norm_num
      · simp [Float.isFinite]
    · intro h_finite
      simp [if_neg (Float.finite_not_nan h_finite), if_neg (Float.finite_ne_inf h_finite), if_neg (Float.finite_ne_neg_inf h_finite)]
  · intro i
    simp [Vector.get_map, replace_float]
    split_ifs with h1 h2 h3
    · simp [Float.isFinite]
    · simp [Float.isFinite]
    · simp [Float.isFinite]
    · exact Float.isFinite_of_not_nan_not_inf h1 h2 h3