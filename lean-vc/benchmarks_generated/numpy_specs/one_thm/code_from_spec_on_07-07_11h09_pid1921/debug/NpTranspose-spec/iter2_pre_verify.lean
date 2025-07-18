namespace NpTranspose

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Fin m → Fin n → α

-- LLM HELPER
def Matrix.of {α : Type} {m n : Nat} (f : Fin m → Fin n → α) : Matrix α m n := f

-- LLM HELPER
def Matrix.get {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Fin m) (j : Fin n) : α := mat i j

-- LLM HELPER
notation mat "[" i "]![" j "]!" => Matrix.get mat i j

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.range m |>.bind fun i => List.range n |>.map fun j => mat ⟨i, by simp⟩ ⟨j, by simp⟩

-- LLM HELPER
theorem Matrix.toList_length {α : Type} {m n : Nat} (mat : Matrix α m n) :
  mat.toList.length = m * n := by
  simp [Matrix.toList]
  rw [List.length_bind]
  simp [List.sum_map_count_eq_length_filter]
  simp [List.length_range]

-- LLM HELPER
theorem Matrix.of_apply {α : Type} {m n : Nat} (f : Fin m → Fin n → α) (i : Fin m) (j : Fin n) :
  Matrix.of f i j = f i j := rfl

def transpose {m n : Nat} (arr : Matrix Int m n) : Matrix Int n m := 
  Matrix.of (fun i j => arr[j]![i]!)

theorem transpose_spec {m n : Nat} (arr : Matrix Int m n) :
  let ret := transpose arr
  (ret.toList.length = n * m) ∧
  (∀ i j : Nat, i < m → j < n → ret[⟨j, by omega⟩]![⟨i, by omega⟩]! = arr[⟨i, by omega⟩]![⟨j, by omega⟩]!) := by
  constructor
  · simp [transpose]
    rw [Matrix.toList_length]
  · intros i j hi hj
    simp [transpose]
    rw [Matrix.of_apply]

end NpTranspose