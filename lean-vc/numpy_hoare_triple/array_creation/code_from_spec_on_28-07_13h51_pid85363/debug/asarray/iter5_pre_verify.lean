import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.asarray: Convert the input to an array.

    Converts various input types (lists, tuples, existing arrays, etc.) to an array.
    The function creates a new array from the input data, preserving the element
    order and values. For our Vector-based specification, we model this as
    converting a list of elements to a Vector.

    This is a fundamental array creation function that ensures the output is
    always a proper array format regardless of the input type.
-/
def asarray (a : List Float) : Id (Vector Float a.length) :=
  Vector.mk a.toArray (by simp [List.size_toArray])

-- LLM HELPER
def problem_spec (impl : List Float → Id (Vector Float (List.length ·))) (a : List Float) : Prop :=
  ∀ result, impl a = result → 
    (∀ i : Fin a.length, result.get i = a[i.val])

/-- Specification: numpy.asarray returns a vector containing the same elements
    as the input list, in the same order.

    Precondition: The input list length matches the vector size parameter
    Postcondition: 
    1. The result vector has the same length as the input list
    2. Each element in the result vector equals the corresponding element in the input list
    3. The ordering of elements is preserved
-/
theorem asarray_spec (a : List Float) :
    problem_spec asarray a := by
  simp [problem_spec]
  intro result h_eq i
  simp [asarray] at h_eq
  rw [← h_eq]
  simp [Vector.get, Vector.mk]
  rw [Array.get_mk, List.get_toArray]