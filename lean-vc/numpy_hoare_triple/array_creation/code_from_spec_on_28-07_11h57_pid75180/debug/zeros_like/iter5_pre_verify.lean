import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.zeros {n : Nat} {T : Type} [Zero T] : Vector T n :=
  ⟨(List.replicate n 0).toArray, by simp [List.length_replicate]⟩

-- LLM HELPER
theorem Vector.get_zeros {n : Nat} {T : Type} [Zero T] (i : Fin n) : 
  (Vector.zeros : Vector T n).get i = 0 := by
  simp [Vector.zeros, Vector.get]
  rw [Array.get_eq_getElem]
  simp [List.getElem_replicate]

/-- Return a vector of zeros with the same length as the input vector.
    This is the 1D version of numpy.zeros_like which creates a new vector
    filled with zeros, having the same size as the input vector. -/
def zeros_like {n : Nat} {T : Type} [Zero T] (a : Vector T n) : Id (Vector T n) :=
  Vector.zeros

/-- Specification: zeros_like returns a vector where every element is 0,
    with the same length as the input vector.
    
    Mathematical properties:
    1. The result has the same length as the input (enforced by type system)
    2. Every element in the result is exactly 0
    3. The result is independent of the input values (only depends on shape)
    4. The result is the additive identity for vector addition
    5. For numeric types, the sum of all elements is zero -/
theorem zeros_like_spec {n : Nat} {T : Type} [Zero T] [Add T] (a : Vector T n) :
    ⦃⌜True⌝⦄
    zeros_like a
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 0) ∧
                 (∀ v : Vector T n, ∀ i : Fin n, 
                   (result.get i + v.get i = v.get i) ∧ 
                   (v.get i + result.get i = v.get i))⌝⦄ := by
  rw [triple_def]
  intro _
  simp [zeros_like, wp_pure]
  constructor
  · intro i
    exact Vector.get_zeros i
  · intro v i
    simp [Vector.get_zeros, zero_add, add_zero]