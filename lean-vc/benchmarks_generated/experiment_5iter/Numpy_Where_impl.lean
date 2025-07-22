import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.where: Return elements chosen from x or y depending on condition.

    For each element, returns x[i] if condition[i] is true, else y[i].
    All three arrays must have the same shape.

    This function enables conditional selection between two arrays.
-/
def numpy_where (condition : Vector Bool n) (x : Vector Float n) (y : Vector Float n) : Id (Vector Float n) :=
  Vector.mk (Array.mk (List.range n |>.map (fun i => 
    if condition.get ⟨i, by rw [List.length_range]; omega⟩ 
    then x.get ⟨i, by rw [List.length_range]; omega⟩ 
    else y.get ⟨i, by rw [List.length_range]; omega⟩)))

-- LLM HELPER
lemma numpy_where_length (condition : Vector Bool n) (x : Vector Float n) (y : Vector Float n) :
    (numpy_where condition x y).val.toArray.size = n := by
  simp [numpy_where, Vector.mk, Array.mk, List.length_map, List.length_range]

-- LLM HELPER  
lemma numpy_where_get_aux (condition : Vector Bool n) (x : Vector Float n) (y : Vector Float n) (i : Fin n) :
    (List.range n |>.map (fun j => 
      if condition.get ⟨j, by rw [List.length_range]; omega⟩ 
      then x.get ⟨j, by rw [List.length_range]; omega⟩ 
      else y.get ⟨j, by rw [List.length_range]; omega⟩)).get i.val = 
    if condition.get i then x.get i else y.get i := by
  have h : i.val < n := i.2
  rw [List.get_map]
  · rw [List.get_range]
    · simp
    · exact h
  · rw [List.length_range]
    exact h

/-- Specification: numpy.where performs element-wise conditional selection.

    Precondition: True (same-size constraint is in the type)
    Postcondition: Each element is selected from x or y based on condition
-/
theorem numpy_where_spec (condition : Vector Bool n) (x : Vector Float n) (y : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_where condition x y
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = if condition.get i then x.get i else y.get i⌝⦄ := by
  simp [Triple.WPSpec, numpy_where]
  intro i
  simp [Vector.get]
  rw [numpy_where_get_aux]