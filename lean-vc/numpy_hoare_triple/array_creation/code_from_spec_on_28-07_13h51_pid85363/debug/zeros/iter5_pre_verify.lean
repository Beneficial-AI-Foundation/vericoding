import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return a new vector of given size, filled with zeros -/
def zeros (n : Nat) (α : Type) [Zero α] : Id (Vector α n) :=
  pure (Vector.replicate n 0)

-- LLM HELPER
lemma zero_add_eq {α : Type} [Add α] [Zero α] [AddMonoid α] (a : α) : 0 + a = a := 
  AddMonoid.zero_add a

-- LLM HELPER  
lemma add_zero_eq {α : Type} [Add α] [Zero α] [AddMonoid α] (a : α) : a + 0 = a := 
  AddMonoid.add_zero a

-- LLM HELPER
lemma mul_zero_eq {α : Type} [Mul α] [Zero α] [MulZeroClass α] (a : α) : a * 0 = 0 :=
  MulZeroClass.mul_zero a

-- LLM HELPER
lemma zero_mul_eq {α : Type} [Mul α] [Zero α] [MulZeroClass α] (a : α) : 0 * a = 0 :=
  MulZeroClass.zero_mul a

-- LLM HELPER
lemma vector_replicate_get (n : Nat) (α : Type) (a : α) (i : Fin n) : 
  (Vector.replicate n a).get i = a := by
  simp [Vector.replicate, Vector.get]

-- LLM HELPER
lemma nat_pos_zero_lt {n : Nat} (h : n > 0) : 0 < n := h

/-- Specification: zeros returns a vector where all elements are zero -/
def zeros_spec (n : Nat) (α : Type) [Zero α] [Add α] [Mul α] (impl : Nat → Type → [Zero α] → Id (Vector α n)) : Prop :=
  ∀ (result : Vector α n), 
    (result = (impl n α).run) →
    (∀ i : Fin n, result.get i = 0) ∧
    (∀ v : Vector α n, ∀ i : Fin n, 
      (result.get i + v.get i = v.get i) ∧ 
      (v.get i + result.get i = v.get i)) ∧
    (∀ scalar : α, ∀ i : Fin n,
      scalar * result.get i = 0) ∧
    (∀ v : Vector α n, ∀ i : Fin n,
      result.get i * v.get i = 0) ∧
    (n > 0 → result.get ⟨0, nat_pos_zero_lt (by assumption)⟩ = 0)

theorem correctness (n : Nat) (α : Type) [Zero α] [Add α] [Mul α] [AddMonoid α] [MulZeroClass α] : zeros_spec n α zeros := by
  intro result h_result
  simp [zeros, Id.run] at h_result
  rw [h_result]
  constructor
  · intro i
    exact vector_replicate_get n α 0 i
  constructor
  · intro v i
    constructor
    · rw [vector_replicate_get]
      exact zero_add_eq (v.get i)
    · rw [vector_replicate_get]
      exact add_zero_eq (v.get i)
  constructor
  · intro scalar i
    rw [vector_replicate_get]
    exact mul_zero_eq scalar
  constructor
  · intro v i
    rw [vector_replicate_get]
    exact zero_mul_eq (v.get i)
  · intro h_pos
    rw [vector_replicate_get]