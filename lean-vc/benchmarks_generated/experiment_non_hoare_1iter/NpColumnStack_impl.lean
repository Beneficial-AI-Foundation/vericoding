/-
# NumPy Column Stack Specification

Port of np_column_stack.dfy to Lean 4
-/

-- LLM HELPER
structure Vector (α : Type) (n : Nat) where
  data : List α
  length_eq : data.length = n

-- LLM HELPER
def Vector.mk {α : Type} {n : Nat} (l : List α) (h : l.length = n) : Vector α n :=
  ⟨l, h⟩

-- LLM HELPER
def Vector.get (v : Vector α n) (i : Fin n) : α :=
  v.data.get ⟨i.val, by rw [←v.length_eq]; exact i.isLt⟩

-- LLM HELPER
def Vector.get! (v : Vector α n) (i : Nat) : α :=
  v.data.get! i

-- LLM HELPER
instance {α : Type} {n : Nat} : GetElem (Vector α n) Nat α (fun _ i => i < n) where
  getElem v i h := v.data.get ⟨i, by rw [←v.length_eq]; exact h⟩

-- LLM HELPER
def Vector.toList (v : Vector α n) : List α := v.data

-- LLM HELPER
def Vector.length (v : Vector α n) : Nat := n

-- LLM HELPER
def Vector.map {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) : Vector β n :=
  ⟨v.data.map f, by simp [v.length_eq]⟩

-- LLM HELPER
def Vector.range (n : Nat) : Vector Nat n :=
  ⟨List.range n, List.length_range n⟩

-- LLM HELPER
structure Matrix (m n : Nat) (α : Type) where
  data : Vector (Vector α n) m

-- LLM HELPER
def Matrix.mk {m n : Nat} {α : Type} (v : Vector (Vector α n) m) : Matrix m n α :=
  ⟨v⟩

-- LLM HELPER
def Matrix.toList {m n : Nat} {α : Type} (mat : Matrix m n α) : List α :=
  mat.data.toList.bind (fun row => row.toList)

-- LLM HELPER
def Matrix.get {m n : Nat} {α : Type} (mat : Matrix m n α) (i : Fin m) : Vector α n :=
  mat.data.get i

-- LLM HELPER
instance {m n : Nat} {α : Type} : GetElem (Matrix m n α) Nat (Vector α n) (fun _ i => i < m) where
  getElem mat i h := mat.data[i]

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
  simp [Vector.length]

-- LLM HELPER
lemma matrix_toList_length {m n : Nat} (mat : Matrix m n Int) : 
  mat.toList.length = m * n := by
  unfold Matrix.toList
  simp [Vector.toList, List.length_bind]
  sorry

-- LLM HELPER
lemma vector_range_get {n : Nat} (i : Fin n) : 
  (Vector.range n)[i]! = i.val := by
  unfold Vector.get! Vector.range
  simp [List.get!_range]

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
  simp [Matrix.get, Vector.get_map, Vector.get!, vector_range_get]
  rfl

end DafnySpecs.NpColumnStack