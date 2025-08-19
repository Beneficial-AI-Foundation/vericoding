import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.less",
  "category": "Comparison",
  "description": "Return the truth value of (x1 < x2) element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.less.html",
  "doc": "Return the truth value of (x1 < x2) element-wise.\n\nParameters\n----------\nx1, x2 : array_like\n    Input arrays. If x1.shape != x2.shape, they must be\n    broadcastable to a common shape (which becomes the shape of the output).\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored. If provided, it must have\n    a shape that the inputs broadcast to. If not provided or None,\n    a freshly-allocated array is returned. A tuple (possible only as a\n    keyword argument) must have length equal to the number of outputs.\nwhere : array_like, optional\n    This condition is broadcast over the input. At locations where the\n    condition is True, the out array will be set to the ufunc result.\n    Elsewhere, the out array will retain its original value.\n    Note that if an uninitialized out array is created via the default\n    out=None, locations within it where the condition is False will\n    remain uninitialized.\n**kwargs\n    For other keyword-only arguments, see the\n    ufunc docs.\n\nReturns\n-------\nout : ndarray or scalar\n    Output array, element-wise comparison of x1 and x2.\n    Typically of type bool, unless dtype=object is passed.\n    This is a scalar if both x1 and x2 are scalars.\n\nSee Also\n--------\ngreater, less_equal, greater_equal, equal, not_equal\n\nExamples\n--------\n>>> np.less([1, 2], [2, 2])\narray([ True, False])",
  "code": "C implementation: ufunc 'less'"
}
-/

/-- numpy.less: Return the truth value of (x1 < x2) element-wise.
    
    Performs element-wise comparison between two vectors and returns a boolean
    vector indicating where elements of x1 are less than corresponding elements
    of x2.
    
    This is a fundamental comparison operation used throughout NumPy for
    conditional operations and boolean indexing.
-/
def less {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Bool n) :=
  Vector.ofFn (fun i => x1.get i < x2.get i)

-- LLM HELPER
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  rfl

-- LLM HELPER
lemma float_lt_trichotomy (a b : Float) : a < b ∨ a = b ∨ b < a := by
  cases' Float.lt_trichotomy a b with h h
  · left; exact h
  · cases' h with h h
    · right; left; exact h
    · right; right; exact h

-- LLM HELPER
lemma float_not_lt_iff_ge (a b : Float) : ¬(a < b) ↔ a ≥ b := by
  rfl

-- LLM HELPER
lemma float_ge_iff_not_lt (a b : Float) : a ≥ b ↔ ¬(a < b) := by
  rfl

/-- Specification: numpy.less returns a boolean vector where each element
    indicates whether the corresponding element in x1 is less than the
    corresponding element in x2.
    
    Mathematical Properties:
    1. Element-wise comparison: result[i] = x1[i] < x2[i]
    2. Strict ordering: For each index i, exactly one of the following holds:
       - x1[i] < x2[i] (result[i] = true)
       - x1[i] ≥ x2[i] (result[i] = false)
    3. Anti-symmetry: If less(x1, x2)[i] = true, then less(x2, x1)[i] = false
    4. Transitivity property: If less(x1, x2)[i] = true and less(x2, x3)[i] = true,
       then less(x1, x3)[i] = true
    5. Special values: NaN comparisons always return false (IEEE 754 standard)
    6. Irreflexivity: x[i] is never less than itself
    
    Precondition: True (no special preconditions for basic comparison)
    Postcondition: For all indices i, result[i] = true iff x1[i] < x2[i]
-/
theorem less_spec {n : Nat} (x1 x2 : Vector Float n) :
    ∀ i : Fin n, (less x1 x2).get i = true ↔ x1.get i < x2.get i := by
  intro i
  simp [less]
  rw [vector_get_ofFn]
  simp

/-- Transitivity property: if less(x1, x2)[i] = true and less(x2, x3)[i] = true,
    then less(x1, x3)[i] = true -/
theorem less_transitivity {n : Nat} (x1 x2 x3 : Vector Float n) :
    ∀ i : Fin n, (less x1 x2).get i = true ∧ (less x2 x3).get i = true → 
                 (less x1 x3).get i = true := by
  intro i h
  simp [less] at h ⊢
  rw [vector_get_ofFn] at h ⊢
  exact Float.lt_trans h.1 h.2

/-- Special handling for NaN values: NaN comparisons always return false
    according to IEEE 754 standard -/
theorem less_nan_handling {n : Nat} (x1 x2 : Vector Float n) :
    ∀ i : Fin n, (x1.get i).isNaN ∨ (x2.get i).isNaN → 
                 (less x1 x2).get i = false := by
  intro i h
  simp [less]
  rw [vector_get_ofFn]
  cases' h with h h
  · exact Float.not_lt_of_isNaN_left h
  · exact Float.not_lt_of_isNaN_right h