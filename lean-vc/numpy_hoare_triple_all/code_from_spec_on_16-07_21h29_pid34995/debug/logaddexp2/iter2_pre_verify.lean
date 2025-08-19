import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.logaddexp2",
  "description": "Logarithm of the sum of exponentiations of the inputs in base-2",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.logaddexp2.html",
  "doc": "Logarithm of the sum of exponentiations of the inputs in base-2.\n\nCalculates log2(2**x1 + 2**x2).",
  "code": "# Universal function (ufunc) implemented in C\n# Logarithm of the sum of exponentiations of the inputs in base-2\n# This function is implemented as a compiled ufunc in NumPy's C extension modules.\n# It provides optimized element-wise operations with support for:\n# - Broadcasting\n# - Type casting and promotion  \n# - Output array allocation\n# - Where parameter for conditional operation\n# - Vectorized execution using SIMD instructions where available"
}
-/

/-- numpy.logaddexp2: Logarithm of the sum of exponentiations of the inputs in base-2.

    Calculates log2(2^x1 + 2^x2) element-wise. This function is mathematically equivalent to
    log2(2^x1 + 2^x2) but is computed in a numerically stable way that avoids overflow for
    large input values.

    The function is useful for numerical computations where you need to add exponentials
    without causing overflow, particularly in machine learning and statistical applications.

    Returns an array of the same shape as the input arrays, containing the base-2 logarithm
    of the sum of exponentiations of corresponding elements.
-/
def numpy_logaddexp2 {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => Float.log2 (Float.exp2 (x1.get i) + Float.exp2 (x2.get i))))

-- LLM HELPER
lemma exp2_pos (x : Float) : Float.exp2 x > 0 := by
  simp [Float.exp2]
  apply Float.exp_pos

-- LLM HELPER
lemma exp2_add_exp2_ge_exp2_max (x y : Float) : Float.exp2 x + Float.exp2 y ≥ Float.exp2 (max x y) := by
  cases' le_total x y with h h
  · simp [max_def, if_pos h]
    have : Float.exp2 x > 0 := exp2_pos x
    linarith
  · simp [max_def, if_neg (not_le.mpr (lt_of_le_of_ne h (Ne.symm (ne_of_lt (lt_of_le_of_ne h (Ne.symm (ne_of_lt h)))))))]
    have : Float.exp2 y > 0 := exp2_pos y
    linarith

-- LLM HELPER
lemma log2_monotone (x y : Float) (hx : x > 0) (hy : y > 0) (h : x ≤ y) : Float.log2 x ≤ Float.log2 y := by
  apply Float.log2_monotone h hx hy

-- LLM HELPER
lemma logaddexp2_ge_max (x y : Float) : Float.log2 (Float.exp2 x + Float.exp2 y) ≥ max x y := by
  have h1 : Float.exp2 x + Float.exp2 y ≥ Float.exp2 (max x y) := exp2_add_exp2_ge_exp2_max x y
  have h2 : Float.exp2 (max x y) > 0 := exp2_pos (max x y)
  have h3 : Float.exp2 x + Float.exp2 y > 0 := by
    have : Float.exp2 x > 0 := exp2_pos x
    have : Float.exp2 y > 0 := exp2_pos y
    linarith
  have h4 := log2_monotone (Float.exp2 (max x y)) (Float.exp2 x + Float.exp2 y) h2 h3 h1
  simp [Float.log2_exp2] at h4
  exact h4

-- LLM HELPER
lemma logaddexp2_le_max_plus_one (x y : Float) : Float.log2 (Float.exp2 x + Float.exp2 y) ≤ max x y + 1 := by
  have h1 : Float.exp2 x + Float.exp2 y ≤ 2 * Float.exp2 (max x y) := by
    cases' le_total x y with h h
    · simp [max_def, if_pos h]
      have : Float.exp2 x ≤ Float.exp2 y := Float.exp2_monotone h
      linarith
    · simp [max_def, if_neg (not_le.mpr (lt_of_le_of_ne h (Ne.symm (ne_of_lt (lt_of_le_of_ne h (Ne.symm (ne_of_lt h)))))))]
      have : Float.exp2 y ≤ Float.exp2 x := Float.exp2_monotone h
      linarith
  have h2 : Float.exp2 (max x y) > 0 := exp2_pos (max x y)
  have h3 : Float.exp2 x + Float.exp2 y > 0 := by
    have : Float.exp2 x > 0 := exp2_pos x
    have : Float.exp2 y > 0 := exp2_pos y
    linarith
  have h4 : 2 * Float.exp2 (max x y) > 0 := by linarith
  have h5 := log2_monotone (Float.exp2 x + Float.exp2 y) (2 * Float.exp2 (max x y)) h3 h4 h1
  have h6 : Float.log2 (2 * Float.exp2 (max x y)) = Float.log2 2 + Float.log2 (Float.exp2 (max x y)) := by
    apply Float.log2_mul
    · linarith
    · exact h2
  simp [Float.log2_exp2, Float.log2_two] at h6
  rw [h6] at h5
  exact h5

/-- Specification: numpy.logaddexp2 returns a vector where each element is the base-2
    logarithm of the sum of exponentiations of the corresponding elements in x1 and x2.

    Precondition: True (no special preconditions - numerically stable for all finite values)
    Postcondition: For all indices i, result[i] = log2(2^x1[i] + 2^x2[i])

    Mathematical properties:
    - Commutativity: logaddexp2(x1, x2) = logaddexp2(x2, x1)
    - Monotonicity: If x1 ≤ y1 and x2 ≤ y2, then logaddexp2(x1, x2) ≤ logaddexp2(y1, y2)
    - Bounds: max(x1, x2) ≤ logaddexp2(x1, x2) ≤ max(x1, x2) + 1
-/
theorem numpy_logaddexp2_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_logaddexp2 x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log2 (Float.exp2 (x1.get i) + Float.exp2 (x2.get i)) ∧
                  result.get i ≥ max (x1.get i) (x2.get i) ∧
                  result.get i ≤ max (x1.get i) (x2.get i) + 1⌝⦄ := by
  apply spec_pure
  intro i
  constructor
  · simp [numpy_logaddexp2, Vector.get_ofFn]
  constructor
  · simp [numpy_logaddexp2, Vector.get_ofFn]
    apply logaddexp2_ge_max
  · simp [numpy_logaddexp2, Vector.get_ofFn]
    apply logaddexp2_le_max_plus_one