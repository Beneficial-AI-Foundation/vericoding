import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Return a new vector of given size, filled with zeros -/
def zeros (n : Nat) (α : Type) [Zero α] : Id (Vector α n) :=
  Vector.replicate n 0

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
    (n > 0 → result.get ⟨0, Nat.zero_lt_succ _⟩ = 0)

theorem correctness (n : Nat) (α : Type) [Zero α] [Add α] [Mul α] : zeros_spec n α zeros := by
  intro result h_result
  rw [zeros, Id.run] at h_result
  rw [h_result]
  constructor
  · intro i
    exact vector_replicate_get n α 0 i
  constructor
  · intro v i
    constructor
    · simp [vector_replicate_get]
    · simp [vector_replicate_get]
  constructor
  · intro scalar i
    simp [vector_replicate_get]
  constructor
  · intro v i
    simp [vector_replicate_get]
  · intro h_pos
    simp [vector_replicate_get]