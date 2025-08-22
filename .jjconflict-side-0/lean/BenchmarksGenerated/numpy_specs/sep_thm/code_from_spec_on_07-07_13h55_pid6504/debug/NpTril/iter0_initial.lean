/-
# NumPy Tril Specification

Port of np_tril.dfy to Lean 4
-/

namespace DafnySpecs.NpTril

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Array (Array α)

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  (mat.toList.map (·.toList)).flatten

-- LLM HELPER
def Matrix.getElem {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Nat) : Array α :=
  mat[i]!

-- LLM HELPER
notation:max mat "[" i "]!" => Matrix.getElem mat i

/-- Extract lower triangular part of matrix -/
def tril {m n : Nat} (a : Matrix Int m n) (k : Int) : Matrix Int m n :=
  Array.mapIdx a fun i row =>
    Array.mapIdx row fun j val =>
      if j ≤ i + k.natAbs then val else 0

/-- Specification: Result has same dimensions -/
theorem tril_dimensions {m n : Nat} (a : Matrix Int m n) (k : Int) :
  let ret := tril a k
  ret.toList.length = m * n := by
  simp [tril, Matrix.toList]
  sorry

/-- Specification: Lower triangular elements are preserved -/
theorem tril_spec {m n : Nat} (a : Matrix Int m n) (k : Int) :
  let ret := tril a k
  ∀ i j : Nat, i < m → j < n →
    if j ≤ i + k.natAbs then ret[i]![j]! = a[i]![j]! else ret[i]![j]! = 0 := by
  intro i j hi hj
  simp [tril]
  split_ifs with h
  · simp [Array.getElem_mapIdx]
  · simp [Array.getElem_mapIdx]

end DafnySpecs.NpTril