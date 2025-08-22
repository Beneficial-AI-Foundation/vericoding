/-
# NumPy Flatten Specification

Port of np_flatten.dfy to Lean 4
-/

namespace DafnySpecs.NpFlatten

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Vector (Vector α n) m

-- LLM HELPER
def Vector.get! {α : Type} {n : Nat} (v : Vector α n) (i : Nat) : α := v.get ⟨i % n, Nat.mod_lt i (by omega)⟩

-- LLM HELPER
def Matrix.get! {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Nat) : Vector α n := mat.get ⟨i % m, Nat.mod_lt i (by omega)⟩

-- LLM HELPER
def flattenRow {n : Nat} (row : Vector Int n) : List Int := row.toList

-- LLM HELPER
def flattenMatrix {m n : Nat} (mat : Matrix Int m n) : List Int :=
  List.join (mat.toList.map flattenRow)

/-- Flatten a 2D matrix to a 1D vector -/
def flatten2 {m n : Nat} (mat : Matrix Int m n) : Vector Int (m * n) := 
  ⟨flattenMatrix mat, by
    simp [flattenMatrix]
    induction mat.toList with
    | nil => simp
    | cons head tail ih =>
      simp [List.map_cons, List.join_cons]
      simp [flattenRow]
      rw [List.length_append]
      rw [Vector.length_toList]
      sorry⟩

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
  simp [flatten2]
  exact Vector.toList_length _

/-- Specification: Elements are correctly indexed -/
theorem flatten2_spec {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  ∀ i j : Nat, i < m → j < n → ret[i * n + j]! = mat[i]![j]! := by
  intro i j hi hj
  simp [flatten2]
  sorry

end DafnySpecs.NpFlatten