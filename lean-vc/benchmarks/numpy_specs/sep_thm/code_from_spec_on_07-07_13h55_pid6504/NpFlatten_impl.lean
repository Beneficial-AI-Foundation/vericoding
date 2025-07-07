/-
# NumPy Flatten Specification

Port of np_flatten.dfy to Lean 4
-/

namespace DafnySpecs.NpFlatten

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Vector (Vector α n) m

-- LLM HELPER
def flattenRow {n : Nat} (row : Vector Int n) : List Int := row.toList

-- LLM HELPER
def flattenMatrix {m n : Nat} (mat : Matrix Int m n) : List Int :=
  List.flatten (mat.toList.map flattenRow)

-- LLM HELPER
instance {α : Type} {n : Nat} : GetElem (Vector α n) Nat α (fun _ i => i < n) where
  getElem v i h := v.get ⟨i, h⟩

-- LLM HELPER
instance {α : Type} {m n : Nat} : GetElem (Matrix α m n) Nat (Vector α n) (fun _ i => i < m) where
  getElem mat i h := mat.get ⟨i, h⟩

-- LLM HELPER
lemma flattenMatrix_length {m n : Nat} (mat : Matrix Int m n) : (flattenMatrix mat).length = m * n := by
  unfold flattenMatrix flattenRow
  rw [List.length_flatten]
  simp [List.map_map, Vector.length_toList]
  rw [List.sum_replicate]

/-- Flatten a 2D matrix to a 1D vector -/
def flatten2 {m n : Nat} (mat : Matrix Int m n) : Vector Int (m * n) := 
  ⟨(flattenMatrix mat).toArray, by
    rw [List.size_toArray]
    exact flattenMatrix_length mat⟩

/-- Specification: The result has correct length -/
theorem flatten2_length {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  ret.toList.length = m * n := by
  unfold flatten2
  simp [Vector.length_toList]
  exact flattenMatrix_length mat

-- LLM HELPER
lemma index_bound_helper {m n : Nat} (i j : Nat) (hi : i < m) (hj : j < n) : i * n + j < m * n := by
  have h_bound : i * n + j < (i + 1) * n := by
    rw [Nat.add_one_mul]
    exact Nat.add_lt_add_left hj (i * n)
  have h_le : (i + 1) * n ≤ m * n := by
    apply Nat.mul_le_mul_right
    exact Nat.succ_le_of_lt hi
  exact Nat.lt_of_lt_of_le h_bound h_le

/-- Specification: Elements are correctly indexed -/
theorem flatten2_spec {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  ∀ i j : Nat, i < m → j < n → ret[i * n + j]'(by
    rw [Vector.length_mk]
    exact index_bound_helper i j ‹i < m› ‹j < n›) = mat[i]'(by assumption)[j]'(by assumption) := by
  intro i j hi hj
  unfold flatten2
  rw [Vector.get_mk]
  unfold flattenMatrix flattenRow
  have h_bound : i * n + j < (flattenMatrix mat).length := by
    rw [flattenMatrix_length]
    exact index_bound_helper i j hi hj
  have h_get : (List.flatten (List.map Vector.toList mat.toList))[i * n + j] = mat[i]'hi[j]'hj := by
    have h_flatten_get : (List.flatten (List.map Vector.toList mat.toList))[i * n + j] = 
      (mat.toList[i])[j] := by
      rw [List.get_flatten_map]
      · exact hi
      · rw [Vector.length_toList]; exact hj
    rw [h_flatten_get, Vector.get_toList, Vector.get_toList]
    rfl
  rw [← h_get]
  rw [Array.get_toArray]
  rfl

end DafnySpecs.NpFlatten