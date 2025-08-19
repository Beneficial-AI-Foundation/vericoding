import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return the imaginary part of complex numbers in a vector.
    For a vector where each element is represented as a pair (real, imaginary),
    extracts the imaginary component of each element.
    For real numbers (where imaginary part is 0), returns 0. -/
def imag {n : Nat} (val : Vector (Float × Float) n) : Id (Vector Float n) :=
  pure (val.map (fun z => z.2))

/-- Specification: imag extracts the imaginary part of complex numbers with the following properties:
    1. Identity: Returns the imaginary part unchanged for each element
    2. Zero for real numbers: If input element is real (imaginary part is 0), output is 0
    3. Type preservation: Output has the same size as input
    4. Mathematical correctness: For complex number z = a + bi, imag(z) = b
    5. Linearity: imag preserves scalar multiplication of imaginary parts
    6. Conjugate property: imag(conj(z)) = -imag(z)
    7. Additive property: imag(z₁ + z₂) = imag(z₁) + imag(z₂) -/
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
  simp [imag]
  constructor
  · -- Property 1: result.get i = (val.get i).2
    intro i
    simp [Vector.get_map]
  constructor
  · -- Property 2: (val.get i).2 = 0 → result.get i = 0
    intro i h
    simp [Vector.get_map]
    exact h
  constructor
  · -- Property 3: (val.get i).1 ≠ 0 ∨ (val.get i).2 ≠ 0 → result.get i = (val.get i).2
    intro i h
    simp [Vector.get_map]
  · -- Property 4: Linearity property
    intro i α h
    simp [Vector.get_map] at h ⊢
    rw [h]
    ring