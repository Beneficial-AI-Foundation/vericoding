namespace NpReshape

-- LLM HELPER
def List.join {α : Type} : List (List α) → List α
  | [] => []
  | xs :: xss => xs ++ List.join xss

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Fin m → Fin n → α

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.join (List.map (fun i => List.map (fun j => mat i j) (List.range n |>.map (fun k => ⟨k, Nat.lt_of_mem_range k⟩))) (List.range m |>.map (fun k => ⟨k, Nat.lt_of_mem_range k⟩)))

-- LLM HELPER
def Matrix.get_safe {α : Type} {m n : Nat} (mat : Matrix α m n) : m > 0 → n > 0 → Nat → Nat → α :=
  fun hm hn i j =>
    let i' := i % m
    let j' := j % n
    mat ⟨i', Nat.mod_lt i' hm⟩ ⟨j', Nat.mod_lt j' hn⟩

-- LLM HELPER
def Int.toNat (x : Int) : Nat := if x > 0 then x.natAbs else 0

def reshape {n : Nat} (arr : Vector Int n) (shape : Vector Int 2) : Matrix Int (if shape[0]! > 0 then shape[0]!.toNat else n / shape[1]!.toNat) (if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat) := 
  fun i j => 
    let idx : Int := i.val * (if shape[1]! > 0 then shape[1]! else n / shape[0]!.toNat) + j.val
    if h : idx.natAbs < n then arr.get ⟨idx.natAbs, h⟩ else 
      if hn : n > 0 then arr.get ⟨0, hn⟩ else 0

-- LLM HELPER
def Matrix.get_safe_general {α : Type} {m n : Nat} (mat : Matrix α m n) (i j : Nat) : Option α :=
  if hm : m > 0 then
    if hn : n > 0 then
      let i' := i % m
      let j' := j % n
      some (mat ⟨i', Nat.mod_lt i' hm⟩ ⟨j', Nat.mod_lt j' hn⟩)
    else none
  else none

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
  unfold reshape Int.toNat
  split_ifs with h4 h5
  · have : shape[0]! * shape[1]! = n := by
      rw [if_pos (And.intro h4 h5)] at h3
      exact h3
    rw [Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    rw [← Int.natAbs_of_nonneg (Int.le_of_lt h4)]
    rw [← Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    rw [← Int.natAbs_mul]
    rw [this]
    rw [Int.natAbs_of_nonneg (Int.le_of_lt (by simp [Int.cast_pos]))]
  · have : n % shape[0]! = 0 := by
      rw [if_neg (fun h => h.2 h5)] at h3
      split_ifs at h3 with h6
      · exact h3
      · exact h3
    rw [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
    rw [Nat.mul_div_cancel']
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
    rw [← Int.natAbs_of_nonneg (Int.le_of_lt h4)]
    rw [← Int.natAbs_mod]
    rw [this]
    simp
  · have : n % shape[1]! = 0 := by
      rw [if_neg (fun h => h.1 h4)] at h3
      split_ifs at h3 with h6
      · exact h3
      · exact h3
    rw [Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    rw [Nat.div_mul_cancel]
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    rw [← Int.natAbs_of_nonneg (Int.le_of_lt h5)]
    rw [← Int.natAbs_mod]
    rw [this]
    simp

-- LLM HELPER
lemma matrix_toList_length {α : Type} {m n : Nat} (mat : Matrix α m n) :
  mat.toList.length = m * n := by
  unfold Matrix.toList
  induction m with
  | zero => simp [List.range_zero]
  | succ m ih => 
    rw [List.range_succ_eq_map, List.map_cons, List.join_cons]
    rw [List.length_append]
    rw [List.length_map]
    rw [List.length_range]
    rw [Nat.succ_mul]
    rw [Nat.add_comm]
    rw [ih]

theorem reshape_spec {n : Nat} (arr : Vector Int n) (shape : Vector Int 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = -1)
  (h2 : ¬(shape[0]! = -1 ∧ shape[1]! = -1))
  (h3 : if shape[0]! > 0 ∧ shape[1]! > 0 then shape[0]! * shape[1]! = n
        else if shape[0]! = -1 then n % shape[1]! = 0
        else n % shape[0]! = 0) :
  let ret := reshape arr shape
  (if shape[0]! > 0 then ret.toList.length / (if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat) = shape[0]!.toNat
   else ret.toList.length / (if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat) = n / shape[1]!.toNat) ∧
  (∀ i : Nat, i < n → 
    let rows := if shape[0]! > 0 then shape[0]!.toNat else n / shape[1]!.toNat
    let cols := if shape[1]! > 0 then shape[1]!.toNat else n / shape[0]!.toNat
    if hr : rows > 0 then
      if hc : cols > 0 then
        ret.get_safe hr hc (i / ret.toList.length) (i % ret.toList.length) = arr[i]!
      else arr[i]! = arr[i]!
    else arr[i]! = arr[i]!) := by
  constructor
  · unfold reshape Matrix.toList Int.toNat
    rw [matrix_toList_length]
    split_ifs with h4 h5
    · rw [Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
      have : shape[0]!.toNat * shape[1]!.toNat = n := by
        have : shape[0]! * shape[1]! = n := by
          rw [if_pos (And.intro h4 h5)] at h3
          exact h3
        unfold Int.toNat
        rw [Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
        rw [← Int.natAbs_of_nonneg (Int.le_of_lt h4)]
        rw [← Int.natAbs_of_nonneg (Int.le_of_lt h5)]
        rw [← Int.natAbs_mul]
        rw [this]
        rw [Int.natAbs_of_nonneg (Int.le_of_lt (by simp [Int.cast_pos]))]
      rw [this, Nat.div_self]
      rw [Int.natAbs_of_nonneg (Int.le_of_lt h5)]
      exact Int.natAbs_pos.mpr h5
    · rw [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
      have : (n / shape[0]!.toNat) * shape[0]!.toNat = n := by
        apply Nat.div_mul_cancel
        have : n % shape[0]! = 0 := by
          rw [if_neg (fun h => h.2 h5)] at h3
          split_ifs at h3 with h6
          · exact h3
          · exact h3
        rw [Nat.dvd_iff_mod_eq_zero]
        rw [Int.toNat, Int.natAbs_of_nonneg (Int.le_of_lt h4)]
        rw [← Int.natAbs_of_nonneg (Int.le_of_lt h4)]
        rw [← Int.natAbs_mod]
        rw [this]
        simp
      rw [this, Nat.div_self]
      rw [Int.natAbs_of_nonneg (Int.le_of_lt h4)]
      exact Int.natAbs_pos.mpr h4
  · intros i hi
    simp only [Int.toNat]
    split_ifs with h4 h5
    · rw [Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
      have h_len : ret.toList.length = n := by
        rw [matrix_toList_length]
        exact matrix_dimensions_correct arr shape h1 h2 h3
      have h_div : i / n = 0 := by
        exact Nat.div_eq_zero_of_lt hi
      have h_mod : i % n = i := by
        exact Nat.mod_eq_of_lt hi
      rw [h_len, h_div, h_mod]
      simp [Matrix.get_safe]
      unfold reshape
      simp only [Int.toNat]
      rw [if_pos h4, if_pos h5]
      simp [Int.natAbs_of_nonneg (Int.le_of_lt h4), Int.natAbs_of_nonneg (Int.le_of_lt h5)]
      rfl
    · simp
    · simp

end NpReshape