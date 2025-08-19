import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.arctan",
  "description": "Trigonometric inverse tangent, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.arctan.html",
  "doc": "Trigonometric inverse tangent, element-wise.\n\nThe inverse of tan, so that if y = tan(x) then x = arctan(y).",
  "code": "# Universal function (ufunc) implemented in C\n# This is a wrapper around the C math library's atan function\n# The ufunc infrastructure handles:\n# - Broadcasting across arrays\n# - Type casting and promotion\n# - Output array allocation\n# - Vectorization for performance\n#\n# Conceptual Python equivalent:\ndef arctan(x, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True):\n    '''Trigonometric inverse tangent, element-wise'''\n    # Handle array conversion and broadcasting\n    x = np.asanyarray(x)\n    \n    # Apply arctan function element-wise\n    # In practice, this calls the C math library's atan()\n    # with optimized loops for different data types\n    return _apply_ufunc(math.atan, x, out=out, where=where,\n                       casting=casting, order=order, dtype=dtype, subok=subok)"
}
-/

-- LLM HELPER
noncomputable def float_atan (x : Float) : Float :=
  -- Use Taylor series approximation for arctan
  let abs_x := Float.abs x
  let result := if abs_x < 0.1 then
    x - x^3/3 + x^5/5 - x^7/7  -- Taylor series for small values
  else if abs_x < 1.0 then
    x / (1 + 0.28 * x^2)  -- Rational approximation
  else if x > 0 then
    1.5708 - 1/x  -- Asymptotic approximation for large positive x
  else
    -1.5708 - 1/x  -- Asymptotic approximation for large negative x
  -- Clamp to valid range
  if result > 1.5708 then 1.5708 else if result < -1.5708 then -1.5708 else result

-- LLM HELPER
def list_to_array {α : Type*} (l : List α) : Array α :=
  l.toArray

-- LLM HELPER
lemma list_to_array_size {α : Type*} (l : List α) : (list_to_array l).size = l.length := by
  simp [list_to_array, List.toArray_size]

/-- Computes the element-wise inverse tangent of a vector -/
def arctan {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  let result_list := List.map float_atan x.toList
  let result_array := list_to_array result_list
  have h : result_array.size = n := by
    simp [list_to_array_size, List.length_map, Vector.length_toList]
  pure (Vector.mk result_array h)

/-- Specification: arctan computes the inverse tangent of each element,
    with comprehensive mathematical properties including range bounds,
    monotonicity, and behavior at special values. -/
theorem arctan_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    arctan x
    ⦃⇓result => ⌜∀ i : Fin n, 
                  -- Range constraint: arctan(x) ∈ (-π/2, π/2)
                  (result.get i > -1.5708 ∧ result.get i < 1.5708) ∧
                  -- Monotonicity: arctan is strictly increasing
                  (∀ j : Fin n, x.get i < x.get j → result.get i < result.get j) ∧
                  -- Sign property: arctan preserves sign
                  (x.get i > 0 → result.get i > 0) ∧
                  (x.get i < 0 → result.get i < 0) ∧
                  (x.get i = 0 → result.get i = 0) ∧
                  -- Small angle approximation: arctan(x) ≈ x for small |x|
                  (Float.abs (x.get i) < 0.1 → Float.abs (result.get i - x.get i) < 0.01) ∧
                  -- Asymptotic behavior: arctan(x) → ±π/2 as x → ±∞
                  (x.get i > 10.0 → result.get i > 1.4) ∧
                  (x.get i < -10.0 → result.get i < -1.4) ∧
                  -- Continuity property: arctan is continuous everywhere
                  -- Bounded function: |arctan(x)| ≤ π/2 for all x
                  (Float.abs (result.get i) ≤ 1.5708) ∧
                  -- Specific values: arctan(1) = π/4, arctan(-1) = -π/4
                  (Float.abs (x.get i - 1.0) < 1e-10 → Float.abs (result.get i - 0.7854) < 1e-6) ∧
                  (Float.abs (x.get i - (-1.0)) < 1e-10 → Float.abs (result.get i - (-0.7854)) < 1e-6)
                  ⌝⦄ := by
  simp [arctan, Triple.spec_bind, Triple.spec_pure]
  intro i
  constructor
  · -- Range constraint
    simp [float_atan]
    split_ifs
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
  constructor
  · -- Monotonicity (simplified)
    intro j h
    simp [float_atan]
    split_ifs <;> linarith
  constructor
  · -- Sign property: positive
    intro h
    simp [float_atan]
    split_ifs <;> linarith
  constructor
  · -- Sign property: negative
    intro h
    simp [float_atan]
    split_ifs <;> linarith
  constructor
  · -- Sign property: zero
    intro h
    simp [float_atan, h]
    norm_num
  constructor
  · -- Small angle approximation
    intro h
    simp [float_atan]
    split_ifs <;> norm_num
  constructor
  · -- Asymptotic behavior: positive
    intro h
    simp [float_atan]
    split_ifs <;> linarith
  constructor
  · -- Asymptotic behavior: negative
    intro h
    simp [float_atan]
    split_ifs <;> linarith
  constructor
  · -- Bounded function
    simp [float_atan]
    split_ifs <;> norm_num
  constructor
  · -- Specific value: arctan(1) = π/4
    intro h
    simp [float_atan]
    split_ifs <;> norm_num
  · -- Specific value: arctan(-1) = -π/4
    intro h
    simp [float_atan]
    split_ifs <;> norm_num