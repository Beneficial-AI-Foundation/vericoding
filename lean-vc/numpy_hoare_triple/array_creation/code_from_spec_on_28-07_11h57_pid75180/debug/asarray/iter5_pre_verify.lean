import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def problem_spec {n : Nat} (asarray_impl : List Float → (h : List.length = n) → Id (Vector Float n)) (a : List Float) (h : a.length = n) : Prop :=
  ⦃⌜a.length = n⌝⦄
  asarray_impl a h
  ⦃⇓result => ⌜∀ i : Fin n, result.get i = a[i.val]'(by rw [h]; exact i.isLt)⌝⦄

/-- numpy.asarray: Convert the input to an array.

    Converts various input types (lists, tuples, existing arrays, etc.) to an array.
    The function creates a new array from the input data, preserving the element
    order and values. For our Vector-based specification, we model this as
    converting a list of elements to a Vector.

    This is a fundamental array creation function that ensures the output is
    always a proper array format regardless of the input type.
-/
def asarray {n : Nat} (a : List Float) (h : a.length = n) : Id (Vector Float n) :=
  pure ⟨a, h⟩

-- LLM HELPER
lemma triple_pure_spec {n : Nat} (a : List Float) (h : a.length = n) :
  ⦃⌜a.length = n⌝⦄ 
  pure ⟨a, h⟩ 
  ⦃⇓result => ⌜∀ i : Fin n, result.get i = a[i.val]'(by rw [h]; exact i.isLt)⌝⦄ := by
  apply Triple.pure
  constructor
  · exact h
  · intro i
    simp [Vector.get]

/-- Specification: numpy.asarray returns a vector containing the same elements
    as the input list, in the same order.

    Precondition: The input list length matches the vector size parameter
    Postcondition: 
    1. The result vector has the same length as the input list
    2. Each element in the result vector equals the corresponding element in the input list
    3. The ordering of elements is preserved
-/
theorem correctness {n : Nat} (a : List Float) (h : a.length = n) :
    problem_spec asarray a h := by
  unfold problem_spec asarray
  exact triple_pure_spec a h