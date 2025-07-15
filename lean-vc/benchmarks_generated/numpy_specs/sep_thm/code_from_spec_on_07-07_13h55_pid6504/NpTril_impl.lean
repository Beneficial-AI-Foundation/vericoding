/-
# NumPy Tril Specification

Port of np_tril.dfy to Lean 4
-/

namespace DafnySpecs.NpTril

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Array (Array α)

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  mat.toList.flatMap (fun row => row.toList)

-- LLM HELPER
instance {α : Type} {m n : Nat} : GetElem (Matrix α m n) Nat (Array α) (fun mat i => i < mat.size) where
  getElem mat i _ := mat[i]!

/-- Extract lower triangular part of matrix -/
def tril {m n : Nat} (a : Matrix Int m n) (k : Int) : Matrix Int m n :=
  Array.mapIdx (fun i row =>
    Array.mapIdx (fun j val =>
      if j ≤ i + k.natAbs then val else 0) row) a

/-- Specification: Result has same dimensions -/
theorem tril_dimensions {m n : Nat} (a : Matrix Int m n) (k : Int) :
  (tril a k).toList.length = m * n := by
  unfold tril Matrix.toList
  have h1 : (Array.mapIdx (fun i row => Array.mapIdx (fun j val => if j ≤ i + k.natAbs then val else 0) row) a).size = a.size := by
    rw [Array.size_mapIdx]
  have h2 : ∀ i, i < a.size → ((Array.mapIdx (fun i row => Array.mapIdx (fun j val => if j ≤ i + k.natAbs then val else 0) row) a)[i]!).size = a[i]!.size := by
    intro i hi
    rw [Array.getElem_mapIdx, Array.size_mapIdx]
  simp [List.length_flatMap]
  rw [← Array.toList_map]
  simp [List.length_map, List.sum_map_count]
  rw [h1]
  congr 1
  ext i
  rw [h2]
  simp

/-- Specification: Lower triangular elements are preserved -/
theorem tril_spec {m n : Nat} (a : Matrix Int m n) (k : Int) :
  ∀ i j : Nat, i < m → j < n →
    if j ≤ i + k.natAbs then (tril a k)[i]![j]! = a[i]![j]! else (tril a k)[i]![j]! = 0 := by
  intro i j hi hj
  unfold tril
  rw [Array.getElem_mapIdx, Array.getElem_mapIdx]
  split_ifs with h
  · rfl  
  · rfl

end DafnySpecs.NpTril