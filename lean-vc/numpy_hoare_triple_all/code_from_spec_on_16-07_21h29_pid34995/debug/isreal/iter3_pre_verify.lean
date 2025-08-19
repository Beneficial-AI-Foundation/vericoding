import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.isreal",
  "category": "Array type testing",
  "description": "Returns a bool array, where True if input element is real",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.isreal.html",
  "doc": "Returns a bool array, where True if input element is real.\n\nIf element has complex type with zero imaginary part, the return value\nfor that element is True.\n\nParameters\n----------\nx : array_like\n    Input array.\n\nReturns\n-------\nout : ndarray, bool\n    Boolean array of same shape as x.\n\nSee Also\n--------\niscomplex\nisrealobj : Return True if x is not a complex type.\n\nExamples\n--------\n>>> np.isreal([1+1j, 1+0j, 4.5, 3, 2, 2j])\narray([False,  True,  True,  True,  True, False])",
  "code": "def isreal(x):\n    \"\"\"\n    Returns a bool array, where True if input element is real.\n    \n    If element has complex type with zero imaginary part, the return value\n    for that element is True.\n    \n    Parameters\n    ----------\n    x : array_like\n        Input array.\n    \n    Returns\n    -------\n    out : ndarray, bool\n        Boolean array of same shape as `x`.\n    \n    See Also\n    --------\n    iscomplex\n    isrealobj : Return True if x is not a complex type.\n    \n    Examples\n    --------\n    >>> np.isreal([1+1j, 1+0j, 4.5, 3, 2, 2j])\n    array([False,  True,  True,  True,  True, False])\n    \n    \"\"\"\n    return imag(x) == 0"
}
-/

/-- Structure representing a complex number with float components -/
structure Complex where
  /-- The real part of the complex number -/
  real : Float
  /-- The imaginary part of the complex number -/
  imag : Float

/-- Returns a bool array, where True if input element is real.
    For complex numbers, checks if imaginary part is zero.
    For numbers with zero imaginary part, returns true for all elements. -/
def isreal {n : Nat} (x : Vector Complex n) : Id (Vector Bool n) :=
  Id.mk (Vector.map (fun c => c.imag == 0.0) x)

-- LLM HELPER
lemma float_eq_iff_beq (a b : Float) : (a = b) ↔ (a == b = true) := by
  constructor
  · intro h
    rw [h]
    exact Float.beq_self_eq_true b
  · intro h
    exact Float.eq_of_beq h

-- LLM HELPER
lemma wp_pure_id {α : Type*} (a : α) (P : α → Prop) : 
    P a → ⦃⌜True⌝⦄ (Id.mk a) ⦃⇓result => ⌜P result⌝⦄ := by
  intro h
  simp [Id.mk]
  exact h

/-- Specification: isreal returns true for elements with zero imaginary parts,
    false for elements with non-zero imaginary parts, with the following properties:
    1. Basic definition: returns true iff imaginary part is zero
    2. Real number detection: pure real numbers (imag = 0) return true
    3. Complex number detection: numbers with non-zero imaginary part return false
    4. Complementary to iscomplex: isreal(x) = not iscomplex(x)
    5. Element-wise operation: each element is tested independently
    6. Mathematical property: real numbers form a subset of complex numbers
    7. Consistency: if real, then can be represented as a + 0i -/
theorem isreal_spec {n : Nat} (x : Vector Complex n) :
    ⦃⌜True⌝⦄
    isreal x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = ((x.get i).imag = 0.0)) ∧
                 (∀ i : Fin n, (x.get i).imag = 0.0 → result.get i = true) ∧
                 (∀ i : Fin n, (x.get i).imag ≠ 0.0 → result.get i = false) ∧
                 (∀ i : Fin n, result.get i = true → (x.get i).imag = 0.0) ∧
                 (∀ i : Fin n, result.get i = false → (x.get i).imag ≠ 0.0) ∧
                 -- Mathematical property: real numbers preserve their real part
                 (∀ i : Fin n, result.get i = true → (x.get i).real = (x.get i).real) ∧
                 -- Complementary property: exactly one of isreal or iscomplex is true
                 (∀ i : Fin n, result.get i = ¬((x.get i).imag ≠ 0.0)) ∧
                 -- Consistency with mathematical definition of real numbers
                 (∀ i : Fin n, result.get i = true ↔ (x.get i).imag = 0.0)⌝⦄ := by
  unfold isreal
  apply wp_pure_id
  constructor
  · intro i
    simp [Vector.get_map]
    rw [← float_eq_iff_beq]
  constructor
  · intro i h
    simp [Vector.get_map]
    rw [float_eq_iff_beq]
    exact h
  constructor
  · intro i h
    simp [Vector.get_map]
    rw [float_eq_iff_beq]
    exact h
  constructor
  · intro i h
    simp [Vector.get_map] at h
    rw [← float_eq_iff_beq] at h
    exact h
  constructor
  · intro i h
    simp [Vector.get_map] at h
    rw [← float_eq_iff_beq] at h
    exact h
  constructor
  · intro i h
    rfl
  constructor
  · intro i
    simp [Vector.get_map]
    rw [← float_eq_iff_beq]
    simp [not_not]
  · intro i
    simp [Vector.get_map]
    rw [← float_eq_iff_beq]