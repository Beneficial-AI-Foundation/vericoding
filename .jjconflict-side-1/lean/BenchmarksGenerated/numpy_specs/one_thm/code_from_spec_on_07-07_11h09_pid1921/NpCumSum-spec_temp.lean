namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  match n with
  | 0 => ⟨#[], rfl⟩
  | m + 1 => 
    let rec cumSumAux (k : Nat) (acc : Int) (hk : k ≤ m + 1) : Vector Int k :=
      match k with
      | 0 => ⟨#[], rfl⟩
      | j + 1 => 
        let hj : j < m + 1 := Nat.lt_of_succ_le hk
        let newAcc := acc + a[j]'hj
        let prevResult := cumSumAux j (acc + a[j]'hj) (Nat.le_of_lt hj)
        ⟨Array.push prevResult.toArray newAcc, by simp [Array.size_push]⟩
    cumSumAux (m + 1) 0 (Nat.le_refl (m + 1))

-- LLM HELPER
lemma cumSum_length {n : Nat} (a : Vector Int n) : (cumSum a).length = n := by
  induction n with
  | zero => simp [cumSum]
  | succ n ih => 
    simp [cumSum]
    rfl

-- LLM HELPER  
lemma cumSum_get_zero {n : Nat} (a : Vector Int n) (h : n > 0) : 
  (cumSum a)[0]'h = a[0]'h := by
  cases n with
  | zero => omega
  | succ m =>
    simp [cumSum]
    rfl

-- LLM HELPER
lemma cumSum_get_succ {n : Nat} (a : Vector Int n) (i : Fin n) (h : i.val > 0) :
  (cumSum a)[i] = (cumSum a)[i.val - 1]'(Nat.sub_lt h (Nat.zero_lt_one)) + a[i] := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    simp [cumSum]
    induction i.val with
    | zero => contradiction
    | succ k ih =>
      simp
      rfl

-- LLM HELPER
lemma pos_of_fin_pos {n : Nat} (i : Fin n) (h : i.val > 0) : n > 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m => exact Nat.zero_lt_succ m

-- LLM HELPER
lemma n_pos_of_fin_pos {n : Nat} (i : Fin n) (h : i.val > 0) : n > 0 := by
  have : i.val < n := i.isLt
  omega

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumSum a)[0]'(by cases n; omega; exact Nat.zero_lt_succ _) = a[0]'(by cases n; omega; exact Nat.zero_lt_succ _)) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by have : i.val < n := i.isLt; omega) + a[i] := by
  constructor
  · intro h
    have h_pos : 0 < n := h
    exact cumSum_get_zero a h_pos
  · intro i h
    have h_sub : i.val - 1 < n := by
      have : i.val < n := i.isLt
      omega
    rw [cumSum_get_succ a i h]
    congr 1
    simp

end NpCumSum