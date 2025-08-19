import Std.Do.Triple
import Std.Tactic.Do

numpy.vectorize function specification and implementation
-/

open Std.Do

/-- Vectorizes a scalar function to operate element-wise on vectors.
    Takes a function f and applies it element-wise to input vectors,
    producing a new vector with the same size. -/
def vectorize {n : Nat} {α β : Type} (f : α → β) (arr : Vector α n) : Id (Vector β n) :=
  pure (Vector.map f arr)

-- LLM HELPER
theorem Vector.get_map_eq {n : Nat} {α β : Type} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v).get i = f (v.get i) := by
  simp [Vector.get, Vector.map]

/-- Specification: vectorize applies the given function element-wise to the input vector.
    The result vector has the same size and each element is the function applied to 
    the corresponding element of the input vector.
    
    Properties verified:
    1. Element-wise application: each output element equals f applied to corresponding input
    2. Size preservation: output vector has same size as input vector
    3. Order preservation: relative positions of elements are maintained
    4. Functional purity: result depends only on function f and input vector
    -/
theorem vectorize_spec {n : Nat} {α β : Type} (f : α → β) (arr : Vector α n) :
    ⦃⌜True⌝⦄
    vectorize f arr
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = f (arr.get i)⌝⦄ := by
  simp [vectorize]
  intro i
  exact Vector.get_map_eq f arr i