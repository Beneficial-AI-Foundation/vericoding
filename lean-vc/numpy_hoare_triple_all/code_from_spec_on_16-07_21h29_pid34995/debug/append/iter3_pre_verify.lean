import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.append: Append values to the end of an array.
    
    For 1D arrays without axis specification, this function flattens both 
    arrays and concatenates them. The result is a 1D array containing all 
    elements from arr followed by all elements from values.
    
    This is a fundamental array manipulation operation that creates a new
    array by joining two arrays end-to-end. Unlike in-place operations,
    this always returns a new array.
-/
def numpy_append {n m : Nat} (arr : Vector Float n) (values : Vector Float m) : 
    Id (Vector Float (n + m)) :=
  pure (arr ++ values)

-- LLM HELPER
lemma vector_get_append_left {α : Type*} {n m : Nat} (v₁ : Vector α n) (v₂ : Vector α m) (i : Fin n) :
    (v₁ ++ v₂).get (i.castAdd m) = v₁.get i := by
  simp [Vector.get_append_left]

-- LLM HELPER
lemma vector_get_append_right {α : Type*} {n m : Nat} (v₁ : Vector α n) (v₂ : Vector α m) (j : Fin m) :
    (v₁ ++ v₂).get (j.natAdd n) = v₂.get j := by
  simp [Vector.get_append_right]

-- LLM HELPER
lemma vector_getElem_eq_get {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) :
    v[i]? = some (v.get i) := by
  simp [Vector.get]

/-- Specification: numpy.append creates a new array containing all elements
    from arr followed by all elements from values.
    
    Precondition: True (no special preconditions for basic append)
    Postcondition: 
    - The first n elements of the result come from arr
    - The next m elements come from values
    - The order of elements is preserved from both input arrays
-/
theorem numpy_append_spec {n m : Nat} (arr : Vector Float n) (values : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_append arr values
    ⦃⇓result => ⌜(∀ i : Fin n, result[i.castAdd m]? = some (arr.get i)) ∧
                (∀ j : Fin m, result[j.natAdd n]? = some (values.get j))⌝⦄ := by
  simp [numpy_append]
  apply pure_post
  constructor
  · intro i
    rw [vector_getElem_eq_get, vector_get_append_left]
  · intro j
    rw [vector_getElem_eq_get, vector_get_append_right]