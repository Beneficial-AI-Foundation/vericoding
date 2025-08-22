namespace NpReshape

-- LLM HELPER
def List.join {α : Type} : List (List α) → List α
  | [] => []
  | xs :: xss => xs ++ List.join xss

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Fin m → Fin n → α

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.join (List.map (fun i => List.map (fun j => mat i j) (List.range n).map (fun k => ⟨k, by simp [List.mem_range]⟩)) (List.range m).map (fun k => ⟨k, by simp [List.mem_range]⟩))

-- LLM HELPER
def Matrix.get_safe {α : Type} {m n : Nat} (mat : Matrix α m n) (i j : Nat) : α :=
  if h1 : i < m then 
    if h2 : j < n then mat ⟨i, h1⟩ ⟨j, h2⟩
    else mat ⟨i, h1⟩ ⟨0, by simp⟩
  else 
    if h2 : j < n then mat ⟨0, by simp⟩ ⟨j, h2⟩
    else mat ⟨0, by simp⟩ ⟨0, by simp⟩

def reshape {n : Nat} (arr : Vector Int n) (shape : Vector Int 2) : Matrix Int (if shape[0]! > 0 then shape[0]! else n / shape[1]!) (if shape[1]! > 0 then shape[1]! else n / shape[0]!) := 
  fun i j => 
    let idx : Int := i.val * (if shape[1]! > 0 then shape[1]! else n / shape[0]!) + j.val
    if h : idx.natAbs < n then arr.get ⟨idx.natAbs, h⟩ else 0

-- LLM HELPER
lemma matrix_dimensions_correct {n : Nat} (arr : Vector Int n) (shape : Vector Int 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = -1)
  (h2 : ¬(shape[0]! = -1 ∧ shape[1]! = -1))
  (h3 : if shape[0]! > 0 ∧ shape[1]! > 0 then shape[0]! * shape[1]! = n
        else if shape[0]! = -1 then n % shape[1]! = 0
        else n % shape[0]! = 0) :
  let ret := reshape arr shape
  let rows := if shape[0]! > 0 then shape[0]! else n / shape[1]!
  let cols := if shape[1]! > 0 then shape[1]! else n / shape[0]!
  rows * cols = n := by
  simp [reshape]
  split_ifs with h4 h5
  · exact h3
  · rw [Nat.mul_div_cancel']
    rw [if_neg h4] at h3
    split_ifs at h3 with h6
    · exact h3
    · exact h3
  · split_ifs at h3 with h6
    · rw [Nat.mul_div_cancel']
      exact h3
    · rw [Nat.mul_div_cancel']
      exact h3

-- LLM HELPER
lemma matrix_toList_length {α : Type} {m n : Nat} (mat : Matrix α m n) :
  mat.toList.length = m * n := by
  simp [Matrix.toList]
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, List.map_append, List.join_append, ih]

theorem reshape_spec {n : Nat} (arr : Vector Int n) (shape : Vector Int 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = -1)
  (h2 : ¬(shape[0]! = -1 ∧ shape[1]! = -1))
  (h3 : if shape[0]! > 0 ∧ shape[1]! > 0 then shape[0]! * shape[1]! = n
        else if shape[0]! = -1 then n % shape[1]! = 0
        else n % shape[0]! = 0) :
  let ret := reshape arr shape
  (if shape[0]! > 0 then ret.toList.length / (if shape[1]! > 0 then shape[1]! else n / shape[0]!) = shape[0]!
   else ret.toList.length / (if shape[1]! > 0 then shape[1]! else n / shape[0]!) = n / shape[1]!) ∧
  (∀ i : Nat, i < n → ret.get_safe (i / ret.toList.length) (i % ret.toList.length) = arr[i]!) := by
  constructor
  · simp [reshape, Matrix.toList]
    split_ifs with h4
    · simp [matrix_toList_length]
      split_ifs with h5
      · rw [Nat.mul_div_cancel_left]
        · rfl
        · simp [h5]
      · rw [Nat.mul_div_cancel_left]
        · rfl
        · apply Nat.div_pos
          · have : shape[0]! * (n / shape[0]!) = n := by
            rw [if_neg h4] at h3
            split_ifs at h3 with h6
            · exact h3
            · exact h3
          · simp [h4]
    · simp [matrix_toList_length]
      split_ifs with h5
      · rw [Nat.mul_div_cancel_left]
        · rfl
        · simp [h5]
      · rw [Nat.mul_div_cancel_left]
        · rfl
        · apply Nat.div_pos
          · have : (n / shape[1]!) * shape[1]! = n := by
            rw [if_neg h4] at h3
            split_ifs at h3 with h6
            · exact h3
            · exact h3
          · simp [h5]
  · intros i hi
    simp [reshape, Matrix.get_safe]
    split_ifs with h4 h5
    · simp [matrix_toList_length]
      have : i / n * shape[1]! + i % n = i := by
        rw [Nat.div_add_mod]
      rw [this]
      simp [hi]
    · simp [matrix_toList_length]
      have : i / n * (n / shape[0]!) + i % n = i := by
        rw [Nat.div_add_mod]
      rw [this]
      simp [hi]

end NpReshape