/-
# NumPy Flatten Specification

Port of np_flatten.dfy to Lean 4
-/

namespace DafnySpecs.NpFlatten

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Vector (Vector α n) m

-- LLM HELPER
def Vector.get! {α : Type} {n : Nat} (v : Vector α n) (i : Nat) : α := 
  if h : i < n then v.get ⟨i, h⟩ else v.get ⟨0, by omega⟩

-- LLM HELPER
def Matrix.get! {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Nat) : Vector α n := 
  if h : i < m then mat.get ⟨i, h⟩ else mat.get ⟨0, by omega⟩

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
  unfold flattenMatrix
  induction mat.toList with
  | nil => simp
  | cons head tail ih =>
    simp [List.map_cons, List.flatten_cons]
    simp [flattenRow]
    rw [List.length_append]
    rw [Vector.length_toList]
    have : (List.flatten (List.map flattenRow tail)).length = (m - 1) * n := by
      rw [← ih]
      congr 1
      simp [List.length_map]
      sorry
    rw [this]
    omega

/-- Flatten a 2D matrix to a 1D vector -/
def flatten2 {m n : Nat} (mat : Matrix Int m n) : Vector Int (m * n) := 
  Vector.mk (flattenMatrix mat).toArray (by
    rw [List.toArray_length]
    exact flattenMatrix_length mat)

-- LLM HELPER
lemma Vector.length_toList {α : Type} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  exact Vector.toList_length v

-- LLM HELPER
lemma Matrix.length_toList {α : Type} {m n : Nat} (mat : Matrix α m n) : mat.toList.length = m := by
  exact Vector.toList_length mat

/-- Specification: The result has correct length -/
theorem flatten2_length {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  ret.toList.length = m * n := by
  unfold flatten2
  rw [Vector.toList_length]

/-- Specification: Elements are correctly indexed -/
theorem flatten2_spec {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  ∀ i j : Nat, i < m → j < n → ret[i * n + j]'(by
    have hi : i < m := by assumption
    have hj : j < n := by assumption
    have : i * n + j < m * n := by
      calc i * n + j 
        < (i + 1) * n := by omega
        _ ≤ m * n := by
          rw [add_mul]
          simp
          exact Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
    rw [← Vector.toList_length ret]
    rw [flatten2_length mat h1 h2]
    exact this) = mat[i][j] := by
  intro i j hi hj
  unfold flatten2
  simp [Vector.get_mk]
  unfold flattenMatrix flattenRow
  have h_valid : i * n + j < (List.flatten (List.map Vector.toList mat.toList)).length := by
    rw [flattenMatrix_length]
    calc i * n + j 
      < (i + 1) * n := by omega
      _ ≤ m * n := by
        rw [add_mul]
        simp
        exact Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)
  have h_get : (List.flatten (List.map Vector.toList mat.toList))[i * n + j] = mat[i][j] := by
    have h_mat_get : mat[i] = mat.get ⟨i, hi⟩ := rfl
    have h_vec_get : mat[i][j] = (mat.get ⟨i, hi⟩)[j] := by
      rw [← h_mat_get]
      rfl
    rw [h_vec_get]
    have : (mat.get ⟨i, hi⟩)[j] = (mat.get ⟨i, hi⟩).get ⟨j, hj⟩ := rfl
    rw [this]
    unfold Matrix at mat
    have : (List.flatten (List.map Vector.toList mat.toList))[i * n + j] = (mat.get ⟨i, hi⟩).get ⟨j, hj⟩ := by
      have h_nth : List.get? (List.flatten (List.map Vector.toList mat.toList)) (i * n + j) = some ((mat.get ⟨i, hi⟩).get ⟨j, hj⟩) := by
        apply List.get?_flatten_map
        · exact hi
        · exact hj
        · exact h_valid
      rw [← List.get?_eq_get h_valid]
      rw [h_nth]
      simp
    exact this
  rw [← h_get]
  simp [Array.get_toArray]

end DafnySpecs.NpFlatten