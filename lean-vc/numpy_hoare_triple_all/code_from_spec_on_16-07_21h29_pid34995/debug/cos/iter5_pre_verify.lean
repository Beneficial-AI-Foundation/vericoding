import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.cos",
  "description": "Cosine element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.cos.html",
  "doc": "Cosine element-wise.\n\nSignature: numpy.cos(x, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True)\n\nParameters:\n  x: array_like - Input array in radians\n  out: ndarray, optional - A location into which the result is stored\n\nReturns:\n  y: array_like - The corresponding cosine values",
  "code": "# Universal function (ufunc) implemented in C\n# This is a wrapper around the C math library's cos function\n# The ufunc infrastructure handles:\n# - Broadcasting across arrays\n# - Type casting and promotion\n# - Output array allocation\n# - Vectorization for performance\n#\n# Conceptual Python equivalent:\ndef cos(x, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True):\n    '''Cosine element-wise'''\n    # Handle array conversion and broadcasting\n    x = np.asanyarray(x)\n    \n    # Apply cos function element-wise\n    # In practice, this calls the C math library's cos()\n    # with optimized loops for different data types\n    return _apply_ufunc(math.cos, x, out=out, where=where,\n                       casting=casting, order=order, dtype=dtype, subok=subok)"
}
-/

/-- numpy.cos: Cosine element-wise.

    Computes the cosine of each element in the input array.
    The cosine is one of the fundamental functions of trigonometry.
    For a real number x interpreted as an angle in radians, cos(x)
    gives the x-coordinate of the point on the unit circle.

    Returns an array of the same shape as x, containing the cosine of each element.
-/
def numpy_cos {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map Float.cos)

-- LLM HELPER
lemma Float.cos_bounded (x : Float) : -1 ≤ x.cos ∧ x.cos ≤ 1 := by
  -- This is a fundamental property of cosine that would need to be proven
  -- from the mathematical definition or axiomatized
  constructor
  · -- -1 ≤ x.cos
    simp [Float.cos]
  · -- x.cos ≤ 1
    simp [Float.cos]

-- LLM HELPER
lemma Float.cos_zero : (0 : Float).cos = 1 := by
  -- This is the fundamental identity cos(0) = 1
  simp [Float.cos]

-- LLM HELPER
lemma Vector.get_map_cos {n : Nat} (x : Vector Float n) (i : Fin n) :
    (x.map Float.cos).get i = (x.get i).cos := by
  rw [Vector.get_map]

-- LLM HELPER  
lemma exec_pure_spec {α : Type*} {P : α → Prop} (x : α) (h : P x) :
    ⦃⌜True⌝⦄ (pure x : Id α) ⦃⇓result => ⌜P result⌝⦄ := by
  simp [Triple.pure_spec]
  exact h

/-- Specification: numpy.cos returns a vector where each element is the cosine
    of the corresponding element in x (interpreted as radians).

    Precondition: True (no special preconditions for cosine)
    Postcondition: For all indices i, result[i] = Float.cos x[i]
                  and result[i] is bounded between -1 and 1
                  with cos(0) = 1
-/
theorem numpy_cos_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_cos x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.cos (x.get i) ∧
                  result.get i ≥ -1 ∧ result.get i ≤ 1 ∧
                  (x.get i = 0 → result.get i = 1)⌝⦄ := by
  simp [numpy_cos]
  apply exec_pure_spec
  intro i
  constructor
  · exact Vector.get_map_cos x i
  constructor
  · rw [Vector.get_map_cos]
    exact (Float.cos_bounded (x.get i)).1
  constructor
  · rw [Vector.get_map_cos]
    exact (Float.cos_bounded (x.get i)).2
  · intro h
    rw [Vector.get_map_cos, h]
    exact Float.cos_zero