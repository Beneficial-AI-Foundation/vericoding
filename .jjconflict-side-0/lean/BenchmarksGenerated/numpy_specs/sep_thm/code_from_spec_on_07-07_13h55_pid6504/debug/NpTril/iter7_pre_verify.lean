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
def Matrix.getElem {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Nat) : Array α :=
  mat[i]!

-- LLM HELPER
instance {α : Type} {m n : Nat} : GetElem (Matrix α m n) Nat (Array α) (fun _ i => i < m) where
  getElem mat i _ := mat[i]!

/-- Extract lower triangular part of matrix -/
def tril {m n : Nat} (a : Matrix Int m n) (k : Int) : Matrix Int m n :=
  Array.mapIdx (fun i row =>
    Array.mapIdx (fun j val =>
      if j ≤ i + k.natAbs then val else 0) row) a

/-- Specification: Result has same dimensions -/
theorem tril_dimensions {m n : Nat} (a : Matrix Int m n) (k : Int) :
  let ret := tril a k
  ret.toList.length = m * n := by
  simp [tril, Matrix.toList]
  have h1 : Array.size ret = Array.size a := by
    simp [Array.size_mapIdx]
  have h2 : ∀ i, i < Array.size ret → Array.size ret[i]! = Array.size a[i]! := by
    intro i hi
    simp [Array.getElem_mapIdx]
  have h3 : ret.toList.length = a.toList.length := by
    simp [Array.size_mapIdx]
  have h4 : (ret.toList.flatMap (fun row => row.toList)).length = ret.toList.length * n := by
    simp [List.length_flatMap, List.sum_replicate]
  rw [h4, h1]
  simp [Matrix.toList]

/-- Specification: Lower triangular elements are preserved -/
theorem tril_spec {m n : Nat} (a : Matrix Int m n) (k : Int) :
  let ret := tril a k
  ∀ i j : Nat, i < m → j < n →
    if j ≤ i + k.natAbs then ret[i]![j]! = a[i]![j]! else ret[i]![j]! = 0 := by
  intro i j hi hj
  simp [tril]
  simp [Array.getElem_mapIdx, hi, hj]
  split_ifs with h
  · rfl
  · rfl

end DafnySpecs.NpTril