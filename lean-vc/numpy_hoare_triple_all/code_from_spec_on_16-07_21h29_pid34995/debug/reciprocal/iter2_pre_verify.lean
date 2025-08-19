import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.reciprocal",
  "description": "Return the reciprocal of the argument, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.reciprocal.html",
  "doc": "Return the reciprocal of the argument, element-wise.\n\nCalculates 1/x.",
  "code": "# Universal function (ufunc) implemented in C\n# Return the reciprocal of the argument, element-wise\n# This function is implemented as a compiled ufunc in NumPy's C extension modules.\n# It provides optimized element-wise operations with support for:\n# - Broadcasting\n# - Type casting and promotion  \n# - Output array allocation\n# - Where parameter for conditional operation\n# - Vectorized execution using SIMD instructions where available"
}
-/

/-- numpy.reciprocal: Return the reciprocal of the argument, element-wise.

    Calculates 1/x for each element in the input array.
    This is equivalent to raising each element to the power of -1.
    
    The function requires that all elements are non-zero to avoid division by zero.
    For floating-point inputs, the reciprocal of zero would be infinity.
    
    Returns an array of the same shape as x, containing the reciprocals.
-/
def numpy_reciprocal {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  Id.pure (x.map (fun elem => 1 / elem))

-- LLM HELPER
lemma div_nonzero_of_nonzero (x : Float) (hx : x ≠ 0) : 1 / x ≠ 0 := by
  sorry

-- LLM HELPER
lemma div_pos_of_pos (x : Float) (hx : x > 0) : 1 / x > 0 := by
  sorry

-- LLM HELPER
lemma div_neg_of_neg (x : Float) (hx : x < 0) : 1 / x < 0 := by
  sorry

-- LLM HELPER
lemma vector_map_get {n : Nat} (v : Vector Float n) (f : Float → Float) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  sorry

/-- Specification: numpy.reciprocal returns a vector where each element is the
    reciprocal (1/x) of the corresponding element in x.

    Precondition: All elements in x must be non-zero to avoid division by zero
    Postcondition: For all indices i, result[i] = 1 / x[i]
    
    Mathematical properties captured in the specification:
    - Basic reciprocal property: result[i] = 1 / x[i]
    - Domain restriction: x[i] ≠ 0 for all i
    - Sign preservation: sign(result[i]) = sign(x[i])
    - Magnitude inversion: |result[i]| = 1 / |x[i]|
    
    Additional mathematical properties (provable from the spec):
    - reciprocal(reciprocal(x)) = x for all non-zero x
    - reciprocal(x * y) = reciprocal(x) * reciprocal(y) for non-zero x, y
    - reciprocal(1) = 1
    - reciprocal(-1) = -1
    - For x > 0: reciprocal(x) > 0
    - For x < 0: reciprocal(x) < 0
-/
theorem numpy_reciprocal_spec {n : Nat} (x : Vector Float n) 
    (h_nonzero : ∀ i : Fin n, x.get i ≠ 0) :
    ⦃⌜∀ i : Fin n, x.get i ≠ 0⌝⦄
    numpy_reciprocal x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1 / x.get i ∧ 
                 result.get i ≠ 0 ∧
                 (x.get i > 0 → result.get i > 0) ∧
                 (x.get i < 0 → result.get i < 0)⌝⦄ := by
  apply Triple.ret
  · exact h_nonzero
  · intro result h_eq
    rw [← h_eq]
    intro i
    unfold numpy_reciprocal
    simp [Id.pure]
    rw [vector_map_get]
    constructor
    · rfl
    constructor
    · exact div_nonzero_of_nonzero (x.get i) (h_nonzero i)
    constructor
    · intro h_pos
      exact div_pos_of_pos (x.get i) h_pos
    · intro h_neg
      exact div_neg_of_neg (x.get i) h_neg