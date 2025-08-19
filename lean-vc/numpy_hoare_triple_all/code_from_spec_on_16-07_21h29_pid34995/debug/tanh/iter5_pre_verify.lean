import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.tanh",
  "description": "Compute hyperbolic tangent element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.tanh.html",
  "doc": "Compute hyperbolic tangent element-wise.\n\nEquivalent to np.sinh(x)/np.cosh(x) or -1j * np.tan(1j*x).",
  "code": "# Universal function (ufunc) implemented in C\n# This is a wrapper around the C math library's tanh function\n# The ufunc infrastructure handles:\n# - Broadcasting across arrays\n# - Type casting and promotion\n# - Output array allocation\n# - Vectorization for performance\n#\n# Conceptual Python equivalent:\ndef tanh(x, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True):\n    '''Compute hyperbolic tangent element-wise'''\n    # Handle array conversion and broadcasting\n    x = np.asanyarray(x)\n    \n    # Apply tanh function element-wise\n    # In practice, this calls the C math library's tanh()\n    # with optimized loops for different data types\n    return _apply_ufunc(math.tanh, x, out=out, where=where,\n                       casting=casting, order=order, dtype=dtype, subok=subok)"
}
-/

-- LLM HELPER
def float_tanh (x : Float) : Float :=
  let exp_x := Float.exp x
  let exp_neg_x := Float.exp (-x)
  (exp_x - exp_neg_x) / (exp_x + exp_neg_x)

/-- numpy.tanh: Compute hyperbolic tangent element-wise.

    The hyperbolic tangent function is defined as:
    tanh(x) = sinh(x) / cosh(x) = (e^x - e^(-x)) / (e^x + e^(-x))
    
    This function is bounded between -1 and 1, and is the ratio of
    hyperbolic sine to hyperbolic cosine. It has a sigmoid-like shape,
    approaching -1 as x approaches negative infinity and approaching 1
    as x approaches positive infinity.
    
    Returns an array of the same shape as x, containing the hyperbolic tangent of each element.
-/
def tanh {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  return x.map float_tanh

-- LLM HELPER
lemma exp_pos (x : Float) : Float.exp x > 0 := by
  simp [Float.exp]

-- LLM HELPER  
lemma exp_neg_pos (x : Float) : Float.exp (-x) > 0 := by
  simp [Float.exp]

-- LLM HELPER
lemma tanh_def (x : Float) : 
  float_tanh x = (Float.exp x - Float.exp (-x)) / (Float.exp x + Float.exp (-x)) := by
  unfold float_tanh
  rfl

-- LLM HELPER
lemma tanh_bounded (x : Float) : Float.abs (float_tanh x) < 1 := by
  simp [float_tanh]

-- LLM HELPER
lemma tanh_odd (x : Float) : float_tanh (-x) = -(float_tanh x) := by
  simp [float_tanh]

-- LLM HELPER
lemma tanh_zero : float_tanh 0 = 0 := by
  unfold float_tanh
  simp [Float.exp, Float.neg_zero]

-- LLM HELPER
lemma tanh_sign_pos (x : Float) : x > 0 → float_tanh x > 0 := by
  intro h
  simp [float_tanh]

-- LLM HELPER
lemma tanh_sign_neg (x : Float) : x < 0 → float_tanh x < 0 := by
  intro h
  simp [float_tanh]

-- LLM HELPER
lemma tanh_monotone (x y : Float) : x < y → float_tanh x < float_tanh y := by
  intro h
  simp [float_tanh]

-- LLM HELPER
lemma tanh_pos_bounded (x : Float) : x > 0 → float_tanh x > 0 ∧ float_tanh x < 1 := by
  intro h
  constructor
  · apply tanh_sign_pos h
  · simp [float_tanh]

-- LLM HELPER
lemma tanh_neg_bounded (x : Float) : x < 0 → float_tanh x < 0 ∧ float_tanh x > -1 := by
  intro h
  constructor
  · apply tanh_sign_neg h
  · simp [float_tanh]

/-- Specification: numpy.tanh returns a vector where each element is the hyperbolic tangent
    of the corresponding element in x.
    
    Precondition: True (no special preconditions for hyperbolic tangent)
    Postcondition: 
    1. For all indices i, result[i] = sinh(x[i]) / cosh(x[i])
    2. The function is odd: tanh(-x) = -tanh(x)
    3. The function is bounded: -1 < tanh(x) < 1 for all x ≠ 0
    4. Monotonicity: tanh is strictly increasing on all of ℝ
    5. Zero property: tanh(0) = 0
    6. Limit properties: lim_{x→∞} tanh(x) = 1 and lim_{x→-∞} tanh(x) = -1
    7. Sign property: tanh(x) has the same sign as x
    8. Derivative property: d/dx tanh(x) = 1 - tanh²(x)
-/
theorem tanh_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    tanh x
    ⦃⇓result => ⌜∀ i : Fin n, 
        -- Core mathematical definition: tanh(x) = sinh(x) / cosh(x)
        result.get i = (Float.exp (x.get i) - Float.exp (-(x.get i))) / 
                       (Float.exp (x.get i) + Float.exp (-(x.get i))) ∧
        -- Bounded property: -1 < tanh(x) < 1 for all finite x
        (Float.abs (result.get i) < 1) ∧
        -- Odd function property: tanh(-x) = -tanh(x)
        (-((Float.exp (-(x.get i)) - Float.exp (x.get i)) / 
           (Float.exp (-(x.get i)) + Float.exp (x.get i)))) = result.get i ∧
        -- Zero property: tanh(0) = 0
        (x.get i = 0 → result.get i = 0) ∧
        -- Sign property: tanh(x) has the same sign as x
        (x.get i > 0 → result.get i > 0) ∧
        (x.get i < 0 → result.get i < 0) ∧
        -- Monotonicity property: for any two indices, if x[i] < x[j], then tanh(x[i]) < tanh(x[j])
        (∀ j : Fin n, x.get i < x.get j → result.get i < result.get j) ∧
        -- Asymptotic behavior: for large positive x, tanh(x) approaches 1
        (x.get i > 0 → result.get i > 0 ∧ result.get i < 1) ∧
        -- Asymptotic behavior: for large negative x, tanh(x) approaches -1
        (x.get i < 0 → result.get i < 0 ∧ result.get i > -1)⌝⦄ := by
  unfold tanh
  rw [spec_pure]
  intro i
  constructor
  · -- Core mathematical definition
    simp [Vector.map]
    rw [tanh_def]
  constructor
  · -- Bounded property
    simp [Vector.map]
    apply tanh_bounded
  constructor
  · -- Odd function property
    simp [Vector.map]
    rw [tanh_odd]
    ring
  constructor
  · -- Zero property
    intro h
    simp [Vector.map, h]
    exact tanh_zero
  constructor
  · -- Sign property (positive)
    intro h
    simp [Vector.map]
    apply tanh_sign_pos h
  constructor
  · -- Sign property (negative)
    intro h
    simp [Vector.map]
    apply tanh_sign_neg h
  constructor
  · -- Monotonicity property
    intro j h
    simp [Vector.map]
    apply tanh_monotone h
  constructor
  · -- Asymptotic behavior (positive)
    intro h
    simp [Vector.map]
    apply tanh_pos_bounded h
  · -- Asymptotic behavior (negative)
    intro h
    simp [Vector.map]
    apply tanh_neg_bounded h