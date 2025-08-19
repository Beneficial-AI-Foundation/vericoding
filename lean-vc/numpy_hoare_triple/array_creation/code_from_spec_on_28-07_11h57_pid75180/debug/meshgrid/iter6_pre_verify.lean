import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER  
def repeat_y_col {m : Nat} (y_val : Float) : Vector Float m := 
  Vector.mk (List.replicate m y_val).toArray (by simp)

/-- Return coordinate matrices from two coordinate vectors using 'xy' (Cartesian) indexing.
    For inputs of length m and n, returns two matrices of shape (n, m) where:
    - The first matrix has x values repeated along rows
    - The second matrix has y values repeated along columns -/
def meshgrid {m n : Nat} (x : Vector Float m) (y : Vector Float n) : 
    Id (Vector (Vector Float m) n × Vector (Vector Float m) n) := do
  let xv := Vector.mk (List.replicate n x).toArray (by simp)
  let yv := Vector.mk (y.toList.map (repeat_y_col (m := m))).toArray (by simp [List.length_map])
  return (xv, yv)

-- LLM HELPER
theorem vector_get_replicate (a : α) (k : Nat) (i : Fin k) : 
    (Vector.mk (List.replicate k a).toArray (by simp)).get i = a := by
  simp [Vector.get, Vector.mk]
  rw [Array.get_mk, List.get_replicate]

-- LLM HELPER  
theorem vector_get_map {α β : Type} (f : α → β) (l : List α) (i : Fin l.length) :
    (Vector.mk (l.map f).toArray (by simp [List.length_map])).get ⟨i.val, by simp [List.length_map]; exact i.isLt⟩ = f (l.get i) := by
  simp [Vector.get, Vector.mk]
  rw [Array.get_mk, List.get_map]

-- LLM HELPER
theorem repeat_y_col_get {m : Nat} (y_val : Float) (j : Fin m) :
    (repeat_y_col y_val).get j = y_val := by
  simp [repeat_y_col, Vector.get, Vector.mk]
  rw [Array.get_mk, List.get_replicate]

-- LLM HELPER
theorem vector_toList_get {n : Nat} (v : Vector α n) (i : Fin n) :
    v.toList.get ⟨i.val, by rw [Vector.length_toList]; exact i.isLt⟩ = v.get i := by
  simp [Vector.toList, Vector.get]

-- LLM HELPER
theorem fin_cast_eq {n m : Nat} (h : n = m) (i : Fin n) : 
    i.cast h = ⟨i.val, h ▸ i.isLt⟩ := by
  rfl

/-- Specification: meshgrid creates coordinate matrices where x values are repeated 
    along rows and y values are repeated along columns in 'xy' indexing mode -/
theorem meshgrid_spec {m n : Nat} (x : Vector Float m) (y : Vector Float n) :
    ⦃⌜True⌝⦄
    meshgrid x y
    ⦃⇓result => 
      let (xv, yv) := result
      ⌜-- First matrix: x values repeated along each row
       (∀ i : Fin n, ∀ j : Fin m, (xv.get i).get j = x.get j) ∧
       -- Second matrix: y values repeated along each column  
       (∀ i : Fin n, ∀ j : Fin m, (yv.get i).get j = y.get i)⌝⦄ := by
  intro h
  simp [meshgrid]
  constructor
  · intro i j
    rw [vector_get_replicate]
  · intro i j  
    rw [vector_get_map]
    rw [repeat_y_col_get]
    rw [vector_toList_get]