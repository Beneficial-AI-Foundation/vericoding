/-
# NumPy Transpose Specification

Port of np_transpose.dfy to Lean 4
-/

namespace DafnySpecs.NpTranspose

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Array (Array α)

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  mat.toList.flatMap (·.toList)

-- LLM HELPER
def Matrix.get {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Nat) (j : Nat) : α :=
  mat[i]![j]!

/-- Transpose a 2D matrix -/
def transpose {m n : Nat} (a : Matrix Int m n) : Matrix Int n m := 
  Array.ofFn (fun j : Fin n => Array.ofFn (fun i : Fin m => Matrix.get a i.val j.val))

-- LLM HELPER
theorem Array.toList_ofFn_length {α : Type} {n : Nat} (f : Fin n → α) :
  (Array.ofFn f).toList.length = n := by
  simp [Array.toList_ofFn]

-- LLM HELPER
theorem Array.flatMap_toList_length {α β : Type} (arr : Array α) (f : α → Array β) :
  (arr.flatMap f).toList.length = (arr.toList.map (fun x => (f x).toList.length)).sum := by
  simp [Array.flatMap_toList]

/-- Specification: Transpose preserves dimensions -/
theorem transpose_dimensions {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ret.toList.length = n * m := by
  unfold transpose Matrix.toList
  simp [Array.toList_ofFn, Array.flatMap_toList_length]
  simp [Array.toList_ofFn_length]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Specification: Elements are correctly transposed -/
theorem transpose_spec {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ∀ i j : Nat, i < m → j < n → Matrix.get ret j i = Matrix.get a i j := by
  intro i j hi hj
  unfold transpose Matrix.get
  simp [Array.getElem_ofFn]

end DafnySpecs.NpTranspose