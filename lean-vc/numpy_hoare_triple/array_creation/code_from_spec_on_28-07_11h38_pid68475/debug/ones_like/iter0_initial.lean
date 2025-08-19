import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return a vector of ones with the same length as the input vector.
    This is the 1D version of numpy.ones_like which creates a new vector
    filled with ones, having the same size as the input vector. -/
def ones_like {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) : Id (Vector T n) :=
  pure (Vector.replicate n 1)

-- LLM HELPER
lemma vector_replicate_get {n : Nat} {T : Type} (x : T) (i : Fin n) :
    (Vector.replicate n x).get i = x := by
  simp [Vector.replicate, Vector.get]

/-- Specification: ones_like returns a vector where every element is 1,
    with the same length as the input vector.
    
    Mathematical properties:
    1. The result has the same length as the input (enforced by type system)
    2. Every element in the result is exactly 1
    3. The result is independent of the input values (only depends on shape) -/
theorem ones_like_spec {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) :
    ⦃⌜True⌝⦄
    ones_like a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1⌝⦄ := by
  simp [ones_like]
  apply triple_ret
  intro i
  exact vector_replicate_get 1 i