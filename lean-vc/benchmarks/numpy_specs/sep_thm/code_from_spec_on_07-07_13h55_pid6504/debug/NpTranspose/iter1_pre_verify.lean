/-
# NumPy Transpose Specification

Port of np_transpose.dfy to Lean 4
-/

namespace DafnySpecs.NpTranspose

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Array (Array α)

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  mat.toList.bind (·.toList)

/-- Transpose a 2D matrix -/
def transpose {m n : Nat} (a : Matrix Int m n) : Matrix Int n m := 
  Array.ofFn (fun j => Array.ofFn (fun i => a[i]![j]!))

/-- Specification: Transpose preserves dimensions -/
theorem transpose_dimensions {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ret.toList.length = n * m := by
  unfold transpose Matrix.toList
  simp [Array.toList_ofFn]
  ring

/-- Specification: Elements are correctly transposed -/
theorem transpose_spec {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ∀ i j : Nat, i < m → j < n → ret[j]![i]! = a[i]![j]! := by
  intro i j hi hj
  unfold transpose
  simp [Array.getElem_ofFn]

end DafnySpecs.NpTranspose