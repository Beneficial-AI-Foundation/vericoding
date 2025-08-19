import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def createXMatrix {m n : Nat} (x : Vector Float m) (_y : Vector Float n) : Vector (Vector Float m) n :=
  Vector.ofFn (fun (_i : Fin n) => x)

-- LLM HELPER
def createYMatrix {m n : Nat} (_x : Vector Float m) (y : Vector Float n) : Vector (Vector Float m) n :=
  Vector.ofFn (fun (i : Fin n) => Vector.ofFn (fun (_j : Fin m) => y.get i))

/-- Return coordinate matrices from two coordinate vectors using 'xy' (Cartesian) indexing.
    For inputs of length m and n, returns two matrices of shape (n, m) where:
    - The first matrix has x values repeated along rows
    - The second matrix has y values repeated along columns -/
def meshgrid {m n : Nat} (x : Vector Float m) (y : Vector Float n) : 
    Id (Vector (Vector Float m) n × Vector (Vector Float m) n) :=
  (createXMatrix x y, createYMatrix x y)

-- LLM HELPER
theorem createXMatrix_spec {m n : Nat} (x : Vector Float m) (y : Vector Float n) :
    ∀ i : Fin n, ∀ j : Fin m, (createXMatrix x y).get i = x := by
  intro i j
  simp [createXMatrix]
  rw [Vector.get_ofFn]

-- LLM HELPER
theorem createYMatrix_spec {m n : Nat} (x : Vector Float m) (y : Vector Float n) :
    ∀ i : Fin n, ∀ j : Fin m, ((createYMatrix x y).get i).get j = y.get i := by
  intro i j
  simp [createYMatrix]
  rw [Vector.get_ofFn, Vector.get_ofFn]

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
  apply triple_pure
  simp [meshgrid]
  constructor
  · intro i j
    simp [createXMatrix]
    rw [Vector.get_ofFn]
  · intro i j
    simp [createYMatrix]
    rw [Vector.get_ofFn, Vector.get_ofFn]