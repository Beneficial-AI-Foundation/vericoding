import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.replicate (n : Nat) (val : T) : Vector T n :=
  ⟨List.replicate n val, List.length_replicate n val⟩

-- LLM HELPER
theorem Vector.get_replicate (n : Nat) (val : T) (i : Fin n) :
    (Vector.replicate n val).get i = val := by
  simp [Vector.replicate, Vector.get]
  rw [List.get_replicate]

/-- Return a vector of zeros with the same length as the input vector.
    This is the 1D version of numpy.zeros_like which creates a new vector
    filled with zeros, having the same size as the input vector. -/
def zeros_like {n : Nat} {T : Type} [Zero T] (a : Vector T n) : Id (Vector T n) :=
  pure (Vector.replicate n 0)

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
  simp [zeros_like]
  apply And.intro
  · intro i
    exact Vector.get_replicate n 0 i
  · intro v i
    constructor
    · rw [Vector.get_replicate n 0 i, zero_add]
    · rw [Vector.get_replicate n 0 i, add_zero]