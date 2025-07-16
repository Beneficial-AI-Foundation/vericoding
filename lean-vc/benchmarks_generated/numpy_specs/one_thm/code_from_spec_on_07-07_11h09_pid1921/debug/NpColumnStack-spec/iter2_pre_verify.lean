namespace NpColumnStack

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Fin m → Fin n → α

-- LLM HELPER
def Matrix.of {α : Type*} {m n : Nat} (f : Fin m → Fin n → α) : Matrix α m n := f

-- LLM HELPER
def Matrix.toList {α : Type*} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.join (List.map (fun i => List.map (fun j => mat i j) (List.range n)) (List.range m))

-- LLM HELPER
instance {α : Type*} {m n : Nat} : GetElem (Matrix α m n) (Fin m) (Fin n → α) (fun _ _ => True) where
  getElem mat i _ := mat i

-- LLM HELPER
instance {α : Type*} {n : Nat} : GetElem (Fin n → α) (Fin n) α (fun _ _ => True) where
  getElem f j _ := f j

-- LLM HELPER
def Matrix.toList_length {α : Type*} {m n : Nat} (mat : Matrix α m n) : mat.toList.length = m * n := by
  simp [Matrix.toList]
  sorry

-- LLM HELPER
def Matrix.of_apply {α : Type*} {m n : Nat} (f : Fin m → Fin n → α) (i : Fin m) (j : Fin n) : 
  Matrix.of f i j = f i j := rfl

def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix Int m n := 
  Matrix.of (fun i j => input[⟨j.val, by simp⟩]![⟨i.val, by simp⟩]!)

theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  (ret.toList.length = m * n) ∧
  (∀ i : Nat, ∀ j : Nat, i < n → j < m → ret[⟨j, by assumption⟩]![⟨i, by assumption⟩]! = input[⟨i, by assumption⟩]![⟨j, by assumption⟩]!) := by
  constructor
  · exact Matrix.toList_length ret
  · intros i j hi hj
    simp [column_stack, Matrix.of_apply]
    rfl

end NpColumnStack