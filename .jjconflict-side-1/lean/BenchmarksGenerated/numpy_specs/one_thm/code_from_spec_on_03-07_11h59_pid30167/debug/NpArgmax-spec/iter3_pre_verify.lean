namespace NpArgmax

/- LLM HELPER -/
def argmax_aux {n : Nat} (arr : Vector Float n) (best_idx : Fin n) (curr_idx : Fin n) : Fin n :=
  if h : curr_idx.val < n - 1 then
    if arr[curr_idx] > arr[best_idx] then
      argmax_aux arr curr_idx ⟨curr_idx.val + 1, Nat.lt_trans (Nat.lt_succ_self _) (Nat.succ_lt_succ h)⟩
    else
      argmax_aux arr best_idx ⟨curr_idx.val + 1, Nat.lt_trans (Nat.lt_succ_self _) (Nat.succ_lt_succ h)⟩
  else
    best_idx

def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  if h' : n = 1 then
    ⟨0, h⟩
  else
    argmax_aux arr ⟨0, h⟩ ⟨0, h⟩

/- LLM HELPER -/
lemma argmax_aux_bounds {n : Nat} (arr : Vector Float n) (best_idx curr_idx : Fin n) :
  (argmax_aux arr best_idx curr_idx).val < n := by
  unfold argmax_aux
  split_ifs with h
  · apply argmax_aux_bounds
  · exact best_idx.isLt

/- LLM HELPER -/
lemma argmax_aux_maximizes {n : Nat} (arr : Vector Float n) (best_idx curr_idx : Fin n) :
  ∀ i : Fin n, i.val < curr_idx.val → arr[argmax_aux arr best_idx curr_idx] ≥ arr[i] := by
  intro i hi
  unfold argmax_aux
  split_ifs with h
  · apply argmax_aux_maximizes
    exact hi
  · have : arr[best_idx] ≥ arr[i] := by
      sorry
    exact this

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
    · have : arr[argmax_aux arr ⟨0, h⟩ ⟨0, h⟩] > arr[i] := by
        sorry
      exact this
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
    · have : arr[argmax_aux arr ⟨0, h⟩ ⟨0, h⟩] ≥ arr[i] := by
        sorry
      exact this

end NpArgmax