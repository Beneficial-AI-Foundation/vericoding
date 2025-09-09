/- 
{
  "name": "numpy.imag",
  "description": "Return the imaginary part of the complex argument",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.imag.html",
  "doc": "Return the imaginary part of the complex argument.\n\nSignature: numpy.imag(val)\n\nParameters:\n  val: array_like - Input array\n\nReturns:\n  out: ndarray or scalar - The imaginary component of the complex argument. If val is real, the type of val is used for the output. If val has complex elements, the returned type is float.",
}
-/

/-  Return the imaginary part of complex numbers in a vector.
    For a vector where each element is represented as a pair (real, imaginary),
    extracts the imaginary component of each element.
    For real numbers (where imaginary part is 0), returns 0. -/

/-  Specification: imag extracts the imaginary part of complex numbers with the following properties:
    1. Identity: Returns the imaginary part unchanged for each element
    2. Zero for real numbers: If input element is real (imaginary part is 0), output is 0
    3. Type preservation: Output has the same size as input
    4. Mathematical correctness: For complex number z = a + bi, imag(z) = b
    5. Linearity: imag preserves scalar multiplication of imaginary parts
    6. Conjugate property: imag(conj(z)) = -imag(z)
    7. Additive property: imag(z₁ + z₂) = imag(z₁) + imag(z₂) -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def imag {n : Nat} (val : Vector (Float × Float) n) : Id (Vector Float n) :=
  sorry

theorem imag_spec {n : Nat} (val : Vector (Float × Float) n) :
    ⦃⌜True⌝⦄
    imag val
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = (val.get i).2) ∧
                 (∀ i : Fin n, (val.get i).2 = 0 → result.get i = 0) ∧
                 (∀ i : Fin n, (val.get i).1 ≠ 0 ∨ (val.get i).2 ≠ 0 → 
                   result.get i = (val.get i).2) ∧
                 (∀ i : Fin n, ∀ (α : Float), 
                   let scaled_complex := (α * (val.get i).1, α * (val.get i).2)
                   result.get i = (val.get i).2 → 
                   α * result.get i = α * (val.get i).2)⌝⦄ := by
  sorry
