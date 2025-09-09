/- 
{
  "name": "numpy.iscomplex",
  "category": "Array type testing",
  "description": "Returns a bool array, where True if input element is complex",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.iscomplex.html",
  "doc": "Returns a bool array, where True if input element is complex.\n\nWhat is tested is whether the input has a non-zero imaginary part, not\nwhether the input type is complex.\n\nParameters\n----------\nx : array_like\n    Input array.\n\nReturns\n-------\nout : ndarray of bools\n    Output array.\n\nSee Also\n--------\nisreal\niscomplexobj : Return True if x is of a complex type.\n\nExamples\n--------\n>>> np.iscomplex([1+1j, 1+0j, 4.5, 3, 2, 2j])\narray([ True, False, False, False, False,  True])",
}
-/

/-  Returns a bool array, where True if input element has non-zero imaginary part.
    For complex numbers, checks if imaginary part is non-zero.
    For real numbers, returns false for all elements. -/

/-  Specification: iscomplex returns true for elements with non-zero imaginary parts,
    false for elements with zero imaginary parts, with the following properties:
    1. Basic definition: returns true iff imaginary part is non-zero
    2. Real number detection: pure real numbers (imag = 0) return false
    3. Complex number detection: numbers with non-zero imaginary part return true
    4. Idempotent on boolean interpretation: the mathematical meaning is preserved
    5. Element-wise operation: each element is tested independently -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Structure representing a complex number with float components -/
structure Complex where
  /-- The real part of the complex number -/
  real : Float
  /-- The imaginary part of the complex number -/
  imag : Float

-- <vc-helpers>
-- </vc-helpers>

def iscomplex {n : Nat} (x : Vector Complex n) : Id (Vector Bool n) :=
  sorry

theorem iscomplex_spec {n : Nat} (x : Vector Complex n) :
    ⦃⌜True⌝⦄
    iscomplex x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = ((x.get i).imag ≠ 0.0)) ∧
                 (∀ i : Fin n, (x.get i).imag = 0.0 → result.get i = false) ∧
                 (∀ i : Fin n, (x.get i).imag ≠ 0.0 → result.get i = true) ∧
                 (∀ i : Fin n, result.get i = true → (x.get i).imag ≠ 0.0) ∧
                 (∀ i : Fin n, result.get i = false → (x.get i).imag = 0.0)⌝⦄ := by
  sorry
