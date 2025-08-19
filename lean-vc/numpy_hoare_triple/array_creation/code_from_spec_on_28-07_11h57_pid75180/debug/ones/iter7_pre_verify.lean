import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma Array.get_replicate (n : Nat) (v : α) (i : Fin n) : (Array.replicate n v).get ⟨i.val, Array.size_replicate n v ▸ i.property⟩ = v := by
  simp [Array.replicate, Array.get]

-- LLM HELPER  
lemma Vector.get_mk_replicate (n : Nat) (v : α) (i : Fin n) : 
  (Vector.mk (Array.replicate n v) (Array.size_replicate n v)).get i = v := by
  simp [Vector.get]
  rw [Array.get_replicate]

-- LLM HELPER
lemma one_gt_zero : (1.0 : Float) > 0 := by
  norm_num

-- LLM HELPER
lemma mul_one_eq (x : Float) : x * 1.0 = x := by
  ring

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
def problem_spec (ones : Nat → Id (Vector Float n)) (n : Nat) : Prop :=
  ⦃⌜True⌝⦄
  ones n
  ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 1.0) ∧ 
               (∀ i j : Fin n, result.get i = result.get j) ∧
               (∀ i : Fin n, result.get i > 0) ∧
               (∀ i : Fin n, ∀ x : Float, x * result.get i = x)⌝⦄

/-- Return a new vector of given size filled with ones.
    
    This function creates a vector where every element is exactly 1.0,
    matching NumPy's ones function behavior for 1D arrays.
-/
def ones (n : Nat) : Id (Vector Float n) :=
  pure (Vector.mk (Array.replicate n 1.0) (by simp [Array.size_replicate]))

theorem correctness (n : Nat) : problem_spec ones n := by
  simp [problem_spec, ones]
  constructor
  · intro i
    rw [Vector.get_mk_replicate]
  constructor
  · intro i j
    rw [Vector.get_mk_replicate, Vector.get_mk_replicate]
  constructor
  · intro i
    rw [Vector.get_mk_replicate]
    exact one_gt_zero
  · intro i x
    rw [Vector.get_mk_replicate]
    exact mul_one_eq x