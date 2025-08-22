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
  (List.range m).flatMap fun i => (List.range n).map fun j => mat ⟨i, Nat.lt_of_mem_range (List.mem_of_mem_range ⟨i, List.mem_range.mp (List.mem_range.mpr (Nat.lt_of_mem_range (List.mem_of_mem_range ⟨i, rfl⟩)))⟩)⟩ ⟨j, Nat.lt_of_mem_range (List.mem_of_mem_range ⟨j, List.mem_range.mp (List.mem_range.mpr (Nat.lt_of_mem_range (List.mem_of_mem_range ⟨j, rfl⟩)))⟩)⟩

-- LLM HELPER
def Matrix.toList_simple {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.join (List.map (fun i => List.map (fun j => mat i j) (List.finRange n)) (List.finRange m))

-- LLM HELPER
theorem Matrix.toList_length {α : Type} {m n : Nat} (mat : Matrix α m n) :
  mat.toList_simple.length = m * n := by
  simp [Matrix.toList_simple]
  simp [List.length_join, List.length_map]
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