import Std.Do.Triple
import Std.Tactic.Do

This function creates a vector where every element is exactly 1.0,
matching NumPy's ones function behavior for 1D arrays.
-/

open Std.Do

-- LLM HELPER
def Vector.mkVector (n : Nat) (f : Fin n → α) : Vector α n :=
  ⟨List.ofFn f, by simp [List.length_ofFn]⟩

-- LLM HELPER
lemma Vector.get_mkVector {α : Type*} (n : Nat) (f : Fin n → α) (i : Fin n) :
  (Vector.mkVector n f).get i = f i := by
  simp [Vector.get, Vector.mkVector, List.get_ofFn]

-- LLM HELPER
lemma Float.mul_one_eq (x : Float) : x * 1.0 = x := by
  simp

/-- Specification: ones returns a vector where all elements are exactly 1.0.
    
    This specification captures the following properties:
    1. **Correctness**: Every element in the returned vector equals 1.0
    2. **Uniformity**: All elements are identical (constant vector)
    3. **Non-negativity**: All elements are positive (1.0 > 0)
    4. **Identity property**: Multiplying any value by an element gives the same value
    5. **Type Safety**: The returned vector has exactly n elements (enforced by type)
    
    Mathematical Properties verified:
    - ∀ i : Fin n, result[i] = 1.0 (all elements are exactly one)
    - ∀ i j : Fin n, result[i] = result[j] (uniformity/constant vector)
    - ∀ i : Fin n, result[i] > 0 (positivity)
    - ∀ i : Fin n, ∀ x : Float, x * result[i] = x (multiplicative identity)
    
    Edge cases handled:
    - When n = 0, returns an empty vector (trivially satisfies all properties)
    - When n > 0, all indices contain exactly 1.0
-/
def ones_spec (f : Nat → Id (Vector Float n)) (n : Nat) : Prop :=
  ⦃⌜True⌝⦄
  f n
  ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 1.0) ∧ 
               (∀ i j : Fin n, result.get i = result.get j) ∧
               (∀ i : Fin n, result.get i > 0) ∧
               (∀ i : Fin n, ∀ x : Float, x * result.get i = x)⌝⦄

/-- Return a new vector of given size filled with ones.
    
    This function creates a vector where every element is exactly 1.0,
    matching NumPy's ones function behavior for 1D arrays.
-/
def ones (n : Nat) : Id (Vector Float n) :=
  pure (Vector.replicate n 1.0)

theorem correctness (n : Nat) : ones_spec ones n := by
  unfold ones_spec ones
  apply triple_pure
  constructor
  · intro i
    simp [Vector.replicate, Vector.get_replicate]
  constructor
  · intro i j
    simp [Vector.replicate, Vector.get_replicate]
  constructor
  · intro i
    simp [Vector.replicate, Vector.get_replicate]
    norm_num
  · intro i x
    simp [Vector.replicate, Vector.get_replicate, Float.mul_one_eq]