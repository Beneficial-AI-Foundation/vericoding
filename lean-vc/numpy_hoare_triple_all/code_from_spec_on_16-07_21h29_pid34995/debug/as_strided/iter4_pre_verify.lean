import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.as_strided: Create a view into the array with the given shape and strides.
    
    Creates a new view of an array with specified shape and strides.
    This is a simplified version that focuses on the core mathematical
    property: creating a view with a different shape but accessing
    elements from the original array based on stride patterns.
    
    For safety, we restrict to cases where the new shape is smaller
    than or equal to the original array size.
-/
def numpy_as_strided {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) : Id (Vector Float m) :=
  Vector.mk (Array.ofFn (fun i => x.get ⟨i.val * stride, by
    have h1 : i.val < m := i.isLt
    have h2 : i.val * stride < m * stride := by
      apply Nat.mul_lt_mul_of_pos_right h1 h_stride_pos
    exact Nat.lt_of_lt_of_le h2 h_valid⟩)) (by simp [Array.size_ofFn])

-- LLM HELPER
def triple_pure {α : Type*} (a : α) : ⦃True⦄ (pure a : Id α) ⦃⇓result => result = a⦄ := by
  simp [pure, Id.pure]

-- LLM HELPER
def triple_bind {α β : Type*} {P : Prop} {Q : α → Prop} {R : β → Prop} 
    (m : Id α) (f : α → Id β) 
    (hm : ⦃P⦄ m ⦃⇓a => Q a⦄) 
    (hf : ∀ a, ⦃Q a⦄ f a ⦃⇓b => R b⦄) : 
    ⦃P⦄ m >>= f ⦃⇓b => R b⦄ := by
  simp [bind, Id.bind]
  exact hf m

/-- Specification: numpy.as_strided creates a view with specified strides.
    
    Precondition: The strided access must be valid (m * stride ≤ n)
    Postcondition: Each element in the result is taken from the original
    array at positions determined by the stride pattern.
    
    For element i in the result, it equals x[i * stride].
-/
theorem numpy_as_strided_spec {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) :
    ⦃m * stride ≤ n ∧ stride > 0⦄
    numpy_as_strided x stride h_valid h_stride_pos
    ⦃⇓result => ∀ i : Fin m, result.get i = x.get ⟨i.val * stride, 
                   by have h1 : i.val < m := i.isLt
                      have h2 : i.val * stride < m * stride := by
                        apply Nat.mul_lt_mul_of_pos_right h1 h_stride_pos
                      exact Nat.lt_of_lt_of_le h2 h_valid⟩⦄ := by
  unfold numpy_as_strided
  apply triple_pure
  intro i
  simp [Vector.get, Array.get_ofFn]