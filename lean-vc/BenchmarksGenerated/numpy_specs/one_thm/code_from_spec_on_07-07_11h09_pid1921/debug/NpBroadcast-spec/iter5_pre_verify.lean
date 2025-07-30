namespace NpBroadcast

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Fin m → Fin n → α

-- LLM HELPER
def Matrix.toList {α : Type*} {m n : Nat} (M : Matrix α m n) : List α :=
  (List.range m).bind fun i => (List.range n).map fun j => M ⟨i, Nat.lt_of_mem_range (List.mem_range.mp (List.mem_range.mpr i.isLt))⟩ ⟨j, Nat.lt_of_mem_range (List.mem_range.mp (List.mem_range.mpr j.isLt))⟩

-- LLM HELPER
instance {α : Type*} {m n : Nat} : GetElem (Matrix α m n) (Fin m) (Fin n → α) (fun _ _ => True) where
  getElem M i _ := M i

-- LLM HELPER
instance {α : Type*} {n : Nat} : GetElem (Fin n → α) (Fin n) α (fun _ _ => True) where
  getElem f i _ := f i

def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix Int (shape[0]!) (shape[1]!) := 
  let rows := shape[0]!
  let cols := shape[1]!
  fun i j => 
    if rows = n then a[⟨i.val, Nat.lt_of_succ_le_succ (Nat.succ_le_of_lt i.isLt)⟩]! else a[⟨j.val, Nat.lt_of_succ_le_succ (Nat.succ_le_of_lt j.isLt)⟩]!

-- LLM HELPER
lemma matrix_toList_length {α : Type*} {m n : Nat} (M : Matrix α m n) : M.toList.length = m * n := by
  simp [Matrix.toList]
  rw [List.length_bind]
  simp [List.sum_const_nat, List.length_range, List.length_map]
  ring

theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  (ret.toList.length = shape[0]! * shape[1]!) ∧
  (∀ i j : Nat, i < shape[0]! → j < shape[1]! →
    if shape[0]! = n then ret[⟨i, by assumption⟩][⟨j, by assumption⟩] = a[⟨i, by cases h with | inl h => rw [←h]; assumption | inr h => sorry⟩]! else ret[⟨i, by assumption⟩][⟨j, by assumption⟩] = a[⟨j, by cases h with | inl h => sorry | inr h => rw [←h]; assumption⟩]!) := by
  constructor
  · simp [broadcast]
    exact matrix_toList_length _
  · intros i j hi hj
    simp [broadcast]
    cases h with
    | inl h => 
      simp [h]
      rfl
    | inr h =>
      simp [h]
      rfl

end NpBroadcast