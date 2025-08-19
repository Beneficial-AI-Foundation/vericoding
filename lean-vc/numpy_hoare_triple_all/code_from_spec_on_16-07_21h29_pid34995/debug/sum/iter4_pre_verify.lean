import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.sum: Sum of array elements over a given axis.

    Computes the sum of all elements in the vector. For empty vectors,
    returns 0 as the identity element of addition.
    
    This is a reduction operation that applies addition across all
    elements to produce a single scalar result.
    
    Mathematical Properties:
    - Commutative: order of elements doesn't affect the final sum
    - Associative: grouping of operations doesn't affect the result
    - Identity element: empty array sum is 0
    - Distributive: sum(a * c) = c * sum(a) for scalar c
    
    From NumPy documentation:
    - Parameters: a (array_like) - Elements to sum
    - Returns: sum_along_axis (ndarray) - Sum of array elements
    - The function handles axis parameter (ignored in 1D case)
    - Supports optional dtype, initial value, and where condition
-/
def sum {n : Nat} (a : Vector Float n) : Id Float :=
  pure (a.toList.foldl (· + ·) 0)

-- LLM HELPER
lemma foldl_zero_prop {n : Nat} (a : Vector Float n) :
  (∀ i : Fin n, a.get i = 0) → a.toList.foldl (· + ·) 0 = 0 := by
  intro h
  have all_zero : ∀ x ∈ a.toList, x = 0 := by
    intro x hx
    have ⟨i, hi⟩ := List.mem_iff_get.mp hx
    rw [←hi]
    have : a.toList.get i = a.get ⟨i.val, by
      rw [Vector.toList_length] at i.isLt
      exact i.isLt⟩ := by
      simp [Vector.toList, Vector.get]
    rw [this]
    apply h
  induction a.toList with
  | nil => simp
  | cons head tail ih =>
    simp [List.foldl]
    have head_zero : head = 0 := all_zero head (List.mem_cons_self head tail)
    rw [head_zero, zero_add]
    apply ih
    intro x hx
    exact all_zero x (List.mem_cons_of_mem head hx)

-- LLM HELPER
lemma empty_vector_sum {a : Vector Float 0} : a.toList.foldl (· + ·) 0 = 0 := by
  have : a.toList = [] := by
    simp [Vector.toList, Vector.mk]
  rw [this]
  simp

/-- Specification: sum computes the sum of all elements in a vector.
    
    The sum operation has several important mathematical properties:
    1. For empty vectors, returns 0 (additive identity)
    2. For non-empty vectors, returns the sum of all elements
    3. The operation is commutative and associative
    4. Linearity: sum(a + b) = sum(a) + sum(b) (element-wise addition)
    5. Scalar multiplication: sum(c * a) = c * sum(a) for scalar c
    
    This specification captures both the basic behavior and key mathematical
    properties that make sum well-defined and predictable.
    
    Precondition: True (works for any vector, including empty)
    Postcondition: Result equals the sum of all elements using fold operation
-/
theorem sum_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    sum a
    ⦃⇓result => ⌜result = (a.toList.foldl (· + ·) 0) ∧ 
                 (n = 0 → result = 0) ∧
                 (∀ i : Fin n, a.get i = 0) → result = 0⌝⦄ := by
  unfold sum
  apply pure_spec_return
  constructor
  · rfl
  constructor
  · intro h
    subst h
    apply empty_vector_sum
  · intro h
    apply foldl_zero_prop
    exact h