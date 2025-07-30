namespace NpBroadcast

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Fin m → Fin n → α

-- LLM HELPER
def Matrix.toList {α : Type*} {m n : Nat} (M : Matrix α m n) : List α :=
  (List.range m).bind fun i => (List.range n).map fun j => M ⟨i, Nat.lt_of_mem_range (List.mem_range.mpr rfl)⟩ ⟨j, Nat.lt_of_mem_range (List.mem_range.mpr rfl)⟩

-- LLM HELPER
instance {α : Type*} {m n : Nat} : GetElem (Matrix α m n) (Fin m) (Fin n → α) (fun _ _ => True) where
  getElem M i _ := M i

-- LLM HELPER
instance {α : Type*} {n : Nat} : GetElem (Fin n → α) (Fin n) α (fun _ _ => True) where
  getElem f i _ := f i

-- LLM HELPER
lemma pos_of_mem_shape {n : Nat} {shape : Vector Int 2} (h : shape[0]! = n ∨ shape[1]! = n) : n > 0 := by
  cases h with
  | inl h1 => 
    have : shape[0]! > 0 := by simp; norm_cast; omega
    rw [h1]; exact this
  | inr h2 => 
    have : shape[1]! > 0 := by simp; norm_cast; omega
    rw [h2]; exact this

def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix Int (shape[0]!.natAbs) (shape[1]!.natAbs) := 
  let rows := shape[0]!.natAbs
  let cols := shape[1]!.natAbs
  fun i j => 
    if rows = n then 
      a[⟨i.val % n, by 
        have hn : n > 0 := by 
          have : shape[0]! = n ∨ shape[1]! = n := by simp
          exact pos_of_mem_shape this
        exact Nat.mod_lt i.val hn⟩]!
    else 
      a[⟨j.val % n, by 
        have hn : n > 0 := by 
          have : shape[0]! = n ∨ shape[1]! = n := by simp
          exact pos_of_mem_shape this
        exact Nat.mod_lt j.val hn⟩]!

-- LLM HELPER
lemma matrix_toList_length {α : Type*} {m n : Nat} (M : Matrix α m n) : M.toList.length = m * n := by
  simp [Matrix.toList]
  rw [List.length_bind]
  simp [List.sum_const_nat, List.length_range, List.length_map]
  ring

theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  (ret.toList.length = shape[0]!.natAbs * shape[1]!.natAbs) ∧
  (∀ i j : Nat, i < shape[0]!.natAbs → j < shape[1]!.natAbs →
    if shape[0]!.natAbs = n then 
      ret[⟨i, by assumption⟩]![⟨j, by assumption⟩] = a[⟨i % n, by 
        have hn : n > 0 := pos_of_mem_shape h
        exact Nat.mod_lt i hn⟩]!
    else 
      ret[⟨i, by assumption⟩]![⟨j, by assumption⟩] = a[⟨j % n, by 
        have hn : n > 0 := pos_of_mem_shape h
        exact Nat.mod_lt j hn⟩]!) := by
  constructor
  · simp [broadcast]
    exact matrix_toList_length _
  · intros i j hi hj
    simp [broadcast]
    split_ifs with h_case
    · simp [h_case]
      congr
      simp [Nat.mod_eq_of_lt]
      rw [←h_case]
      exact hi
    · simp
      congr
      simp [Nat.mod_eq_of_lt]
      cases h with
      | inl h1 => 
        have : shape[1]!.natAbs = n := by
          simp at h_case
          cases h with
          | inl h_left => contradiction
          | inr h_right => simp [h_right]
        rw [←this]
        exact hj
      | inr h2 => 
        simp [h2]
        exact hj

end NpBroadcast