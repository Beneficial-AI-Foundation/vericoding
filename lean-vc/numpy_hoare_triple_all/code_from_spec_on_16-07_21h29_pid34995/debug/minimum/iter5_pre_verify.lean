import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.minimum: Element-wise minimum of array elements.

    Compare two arrays and returns a new array containing the element-wise minima.
    If one of the elements being compared is NaN, then that element is returned.
    
    This is different from numpy.min which returns a single minimum value.
    This function performs element-wise comparison and returns a new array.
    
    Binary universal function: minimum(x1, x2)
    
    Parameters:
    - x1, x2: Vector Float n - Input vectors of the same size
    
    Returns:
    - Vector Float n - The element-wise minimum of x1 and x2
-/
def minimum {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => min (x1.get i) (x2.get i)))

-- LLM HELPER
lemma vector_get_ofFn {n : Nat} (f : Fin n → Float) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  rfl

-- LLM HELPER
lemma min_comm (a b : Float) : min a b = min b a := by
  simp [min]

-- LLM HELPER
lemma min_le_left (a b : Float) : min a b ≤ a := by
  simp [min]

-- LLM HELPER
lemma min_le_right (a b : Float) : min a b ≤ b := by
  simp [min]

-- LLM HELPER
lemma min_eq_left_or_right (a b : Float) : min a b = a ∨ min a b = b := by
  simp [min]
  by_cases h : a ≤ b
  · left
    simp [h]
  · right
    simp [h]

/-- Specification: numpy.minimum returns a vector where each element is the minimum
    of the corresponding elements from x1 and x2.

    Mathematical properties:
    1. Commutativity: min(a, b) = min(b, a)
    2. Associativity: min(min(a, b), c) = min(a, min(b, c))
    3. Idempotency: min(a, a) = a
    4. Element-wise operation: result[i] = min(x1[i], x2[i]) for all i
    5. NaN propagation: if either x1[i] or x2[i] is NaN, result[i] is NaN
    
    Precondition: True (no special preconditions for element-wise minimum)
    Postcondition: For all indices i, result[i] = min(x1[i], x2[i])
-/
theorem minimum_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    minimum x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = min (x1.get i) (x2.get i) ∧
                 -- Commutativity property
                 (minimum x1 x2).get i = (minimum x2 x1).get i ∧
                 -- Bounded property: result is bounded by inputs
                 result.get i ≤ x1.get i ∧ result.get i ≤ x2.get i ∧
                 -- Definitional property: result equals one of the inputs
                 (result.get i = x1.get i ∨ result.get i = x2.get i)⌝⦄ := by
  apply Triple.pure_post
  intro i
  constructor
  · -- result.get i = min (x1.get i) (x2.get i)
    unfold minimum
    simp [vector_get_ofFn]
  constructor
  · -- Commutativity property
    unfold minimum
    simp [vector_get_ofFn, min_comm]
  constructor
  · -- result.get i ≤ x1.get i
    unfold minimum
    simp [vector_get_ofFn, min_le_left]
  constructor
  · -- result.get i ≤ x2.get i
    unfold minimum
    simp [vector_get_ofFn, min_le_right]
  · -- result.get i = x1.get i ∨ result.get i = x2.get i
    unfold minimum
    simp [vector_get_ofFn]
    apply min_eq_left_or_right