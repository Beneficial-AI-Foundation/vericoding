/-
# NumPy Column Stack Specification

Port of np_column_stack.dfy to Lean 4
-/

import benchmarks.MatrixDef

namespace DafnySpecs.NpColumnStack

/-- Stack vectors as columns to form a matrix -/
def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix m n Int := 
  Matrix.mk (Vector.map (fun row_idx => 
    Vector.map (fun col_idx => input[col_idx]![row_idx]!) (Vector.range n)
  ) (Vector.range m))

-- LLM HELPER
lemma vector_length_eq_m {m n : Nat} (input : Vector (Vector Int m) n) 
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  ∀ i : Fin n, input[i].length = m := by
  intro i
  rw [Vector.length_eq_toList_length]
  exact h2 i

-- LLM HELPER
lemma matrix_toList_length {m n : Nat} (mat : Matrix m n Int) : 
  mat.toList.length = m * n := by
  cases mat with
  | mk v => 
    simp [Matrix.toList, Vector.toList_length]
    rw [Vector.length_eq_toList_length]
    simp [Vector.map_length, Vector.range_length]

-- LLM HELPER
lemma vector_range_get {n : Nat} (i : Fin n) : 
  (Vector.range n)[i]! = i.val := by
  simp [Vector.get_range]

/-- Specification: The result has correct dimensions -/
theorem column_stack_dimensions {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ret.toList.length = m * n := by
  unfold column_stack
  apply matrix_toList_length

/-- Specification: Elements are correctly placed -/
theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ∀ i : Nat, ∀ j : Nat, i < n → j < m → ret[j]![i]! = input[i]![j]! := by
  intro i j hi hj
  unfold column_stack
  simp [Matrix.get, Vector.get_map]
  have hi_fin : i < n := hi
  have hj_fin : j < m := hj
  simp [vector_range_get]
  congr

end DafnySpecs.NpColumnStack