namespace NpReshape

-- LLM HELPER
def List.join {α : Type} : List (List α) → List α
  | [] => []
  | xs :: xss => xs ++ List.join xss

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Fin m → Fin n → α

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.join (List.map (fun i => List.map (fun j => mat i j) (List.range n |>.map (fun k => ⟨k, by 
    simp only [List.mem_range]
    exact k.2⟩))) (List.range m |>.map (fun k => ⟨k, by 
    simp only [List.mem_range]
    exact k.2⟩)))

-- LLM HELPER
def Matrix.get_safe {α : Type} {m n : Nat} (mat : Matrix α m n) (i j : Nat) : α :=
  if h1 : i < m then 
    if h2 : j < n then mat ⟨i, h1⟩ ⟨j, h2⟩
    else if h3 : 0 < n then mat ⟨i, h1⟩ ⟨0, h3⟩ else 
      if h4 : 0 < m then mat ⟨0, h4⟩ ⟨0, by simp⟩ else mat ⟨0, h1⟩ ⟨0, by simp⟩
  else 
    if h2 : j < n then 
      if h4 : 0 < m then mat ⟨0, h4⟩ ⟨j, h2⟩ else mat ⟨0, by simp⟩ ⟨j, h2⟩
    else if h3 : 0 < n ∧ 0 < m then mat ⟨0, h3.2⟩ ⟨0, h3.1⟩ else
      if h4 : 0 < m ∧ 0 < n then mat ⟨0, h4.1⟩ ⟨0, h4.2⟩ else mat ⟨0, by simp⟩ ⟨0, by simp⟩

-- LLM HELPER
def Int.toNat (x : Int) : Nat := if x > 0 then x.natAbs else 0

def reshape {n : Nat} (arr : Vector Int n) (shape : Vector Int 2) : Matrix Int (if shape[0]! > 0 then shape[0]!.toNat else n / shape[1]!.toNat) (if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat) := 
  fun i j => 
    let idx : Int := i.val * (if shape[1]! > 0 then shape[1]! else n / shape[0]!.toNat) + j.val
    if h : idx.natAbs < n then arr.get ⟨idx.natAbs, h⟩ else 0

-- LLM HELPER
lemma matrix_dimensions_correct {n : Nat} (arr : Vector Int n) (shape : Vector Int 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = -1)
  (h2 : ¬(shape[0]! = -1 ∧ shape[1]! = -1))
  (h3 : if shape[0]! > 0 ∧ shape[1]! > 0 then shape[0]! * shape[1]! = n
        else if shape[0]! = -1 then n % shape[1]! = 0
        else n % shape[0]! = 0) :
  let ret := reshape arr shape
  let rows := if shape[0]! > 0 then shape[0]!.toNat else n / shape[1]!.toNat
  let cols := if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat
  rows * cols = n := by
  simp only [reshape, Int.toNat]
  split_ifs with h4 h5
  · have : shape[0]! * shape[1]! = n := by
      rw [if_pos (And.intro h4 h5)] at h3
      exact h3
    simp only [Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    exact this
  · have : n % shape[0]! = 0 := by
      rw [if_neg (fun h => h.2 h5)] at h3
      split_ifs at h3 with h6
      · exact h3
      · exact h3
    simp only [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
    rw [Nat.mul_div_cancel']
    rw [Nat.dvd_iff_mod_eq_zero]
    simp only [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
    exact this
  · have : n % shape[1]! = 0 := by
      rw [if_neg (fun h => h.1 h4)] at h3
      split_ifs at h3 with h6
      · exact h3
      · exact h3
    simp only [Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    rw [Nat.mul_div_cancel']
    rw [Nat.dvd_iff_mod_eq_zero]
    simp only [Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    exact this

-- LLM HELPER
lemma matrix_toList_length {α : Type} {m n : Nat} (mat : Matrix α m n) :
  mat.toList.length = m * n := by
  simp only [Matrix.toList]
  induction m with
  | zero => simp
  | succ m ih => simp only [List.range_succ, List.map_append, List.join_append, ih]

theorem reshape_spec {n : Nat} (arr : Vector Int n) (shape : Vector Int 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = -1)
  (h2 : ¬(shape[0]! = -1 ∧ shape[1]! = -1))
  (h3 : if shape[0]! > 0 ∧ shape[1]! > 0 then shape[0]! * shape[1]! = n
        else if shape[0]! = -1 then n % shape[1]! = 0
        else n % shape[0]! = 0) :
  let ret := reshape arr shape
  (if shape[0]! > 0 then ret.toList.length / (if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat) = shape[0]!.toNat
   else ret.toList.length / (if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat) = n / shape[1]!.toNat) ∧
  (∀ i : Nat, i < n → ret.get_safe (i / ret.toList.length) (i % ret.toList.length) = arr[i]!) := by
  constructor
  · simp only [reshape, Matrix.toList, Int.toNat]
    rw [matrix_toList_length]
    split_ifs with h4 h5
    · simp only [Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
      have : shape[0]!.toNat * shape[1]!.toNat = n := by
        have : shape[0]! * shape[1]! = n := by
          rw [if_pos (And.intro h4 h5)] at h3
          exact h3
        simp only [Int.toNat, Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
        exact this
      rw [this, Nat.div_self]
      rw [Ne.def, Nat.zero_div]
      simp only [Int.natAbs_of_nonneg (Int.le_of_lt h5)]
      exact Int.natAbs_pos.mpr h5
    · simp only [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
      have : (n / shape[0]!.toNat) * shape[0]!.toNat = n := by
        apply Nat.div_mul_cancel
        have : n % shape[0]! = 0 := by
          rw [if_neg (fun h => h.2 h5)] at h3
          split_ifs at h3 with h6
          · exact h3
          · exact h3
        rw [Nat.dvd_iff_mod_eq_zero]
        simp only [Int.toNat, Int.natAbs_of_nonneg (Int.le_of_lt h4)]
        exact this
      rw [this, Nat.div_self]
      rw [Ne.def, Nat.zero_div]
      simp only [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
      exact Int.natAbs_pos.mpr h4
  · intros i hi
    simp only [reshape, Matrix.get_safe]
    have h_len : ret.toList.length = n := by
      rw [matrix_toList_length]
      exact matrix_dimensions_correct arr shape h1 h2 h3
    have h_div : i / n = 0 := by
      exact Nat.div_eq_zero_of_lt hi
    have h_mod : i % n = i := by
      exact Nat.mod_eq_of_lt hi
    rw [h_len, h_div, h_mod]
    simp only [Nat.zero_lt_one]
    rfl

end NpReshape