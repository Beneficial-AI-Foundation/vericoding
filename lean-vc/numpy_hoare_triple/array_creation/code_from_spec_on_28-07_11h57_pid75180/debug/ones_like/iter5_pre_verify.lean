import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return a vector of ones with the same length as the input vector.
    This is the 1D version of numpy.ones_like which creates a new vector
    filled with ones, having the same size as the input vector. -/
def ones_like {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) : Id (Vector T n) :=
  Id.pure (Vector.mk (Array.mk (List.replicate n 1)) (by simp))

-- LLM HELPER
lemma replicate_length {T : Type} (n : Nat) (x : T) : (List.replicate n x).length = n := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate, ih]

-- LLM HELPER
lemma replicate_get {T : Type} (n : Nat) (x : T) (i : Fin n) : 
    (List.replicate n x).get ⟨i.val, by rw [replicate_length]; exact i.isLt⟩ = x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases' i.val with j
    · simp [List.replicate, List.get]
    · simp [List.replicate, List.get]
      apply ih
      exact ⟨j, Nat.lt_of_succ_lt_succ i.isLt⟩

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
  unfold ones_like
  apply Triple.pure
  simp [Vector.get, Vector.mk]
  intro i
  have h : (Array.mk (List.replicate n 1))[i] = (List.replicate n 1).get ⟨i.val, by rw [replicate_length]; exact i.isLt⟩ := by
    simp [Array.getElem_mk]
  rw [h]
  exact replicate_get n 1 i