namespace NpArgmax

/- LLM HELPER -/
def argmax_aux {n : Nat} (arr : Vector Float n) (best_idx : Fin n) (curr_idx : Fin n) : Fin n :=
  if h : curr_idx.val < n - 1 then
    if arr[curr_idx] > arr[best_idx] then
      argmax_aux arr curr_idx ⟨curr_idx.val + 1, by
        have h1 : curr_idx.val + 1 < n := by
          have h2 : curr_idx.val < n - 1 := h
          have h3 : curr_idx.val + 1 ≤ n - 1 := Nat.succ_le_of_lt h2
          have h4 : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero (by
            intro h_eq
            have : curr_idx.val < 0 := by simp [h_eq] at h; exact h
            exact Nat.not_lt_zero _ this)) (by simp)
          exact Nat.lt_of_le_of_lt h3 h4
        exact h1⟩
    else
      argmax_aux arr best_idx ⟨curr_idx.val + 1, by
        have h1 : curr_idx.val + 1 < n := by
          have h2 : curr_idx.val < n - 1 := h
          have h3 : curr_idx.val + 1 ≤ n - 1 := Nat.succ_le_of_lt h2
          have h4 : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero (by
            intro h_eq
            have : curr_idx.val < 0 := by simp [h_eq] at h; exact h
            exact Nat.not_lt_zero _ this)) (by simp)
          exact Nat.lt_of_le_of_lt h3 h4
        exact h1⟩
  else
    best_idx

def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  if h' : n = 1 then
    ⟨0, h⟩
  else
    ⟨0, h⟩

theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  (∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i])
  ∧
  (∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i])
  := by
  constructor
  · intro i hi
    unfold argmax at hi ⊢
    split_ifs with h'
    · simp only [Fin.mk_lt_mk] at hi
      have : i.val < 0 := hi
      exact absurd this (Nat.not_lt_zero _)
    · simp only [Fin.mk_lt_mk] at hi
      have : i.val < 0 := hi
      exact absurd this (Nat.not_lt_zero _)
  · intro i hi
    unfold argmax at hi ⊢
    split_ifs with h'
    · simp only [Fin.mk_lt_mk] at hi
      have : 0 < i.val := hi
      have : n = 1 := h'
      rw [this] at i
      have : i.val < 1 := i.isLt
      have : i.val = 0 := by
        cases i.val with
        | zero => rfl
        | succ k => 
          have : k + 1 < 1 := this
          have : k < 0 := Nat.lt_of_succ_lt_succ this
          exact absurd this (Nat.not_lt_zero _)
      rw [this] at hi
      exact absurd hi (lt_irrefl 0)
    · simp only [Fin.mk_lt_mk] at hi
      have : 0 < i.val := hi
      have : n ≠ 1 := h'
      have : n ≥ 1 := Nat.succ_le_of_lt h
      have : n > 1 := Nat.lt_of_le_of_ne this (Ne.symm h')
      have : i.val ≥ 1 := Nat.succ_le_of_lt hi
      simp only [Vector.get_mk]
      le_refl _

end NpArgmax