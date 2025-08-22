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
def Matrix.toList_simple {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.join (List.map (fun i => List.map (fun j => mat i j) (List.finRange n)) (List.finRange m))

-- LLM HELPER
theorem Matrix.toList_length {α : Type} {m n : Nat} (mat : Matrix α m n) :
  mat.toList_simple.length = m * n := by
  simp [Matrix.toList_simple]
  rw [List.length_join, List.map_map]
  simp [List.length_map, List.length_finRange]
  rw [List.sum_map_const]
  simp [List.length_finRange]

-- LLM HELPER
theorem Matrix.of_apply {α : Type} {m n : Nat} (f : Fin m → Fin n → α) (i : Fin m) (j : Fin n) :
  Matrix.of f i j = f i j := rfl

def transpose {m n : Nat} (arr : Matrix Int m n) : Matrix Int n m := 
  Matrix.of (fun i j => arr[j]![i]!)

theorem transpose_spec {m n : Nat} (arr : Matrix Int m n) :
  let ret := transpose arr
  (ret.toList_simple.length = n * m) ∧
  (∀ i j : Nat, i < m → j < n → ret[⟨j, hj⟩]![⟨i, hi⟩]! = arr[⟨i, hi⟩]![⟨j, hj⟩]!) := by
  constructor
  · simp [transpose]
    rw [Matrix.toList_length]
  · intros i j hi hj
    simp [transpose]
    rfl