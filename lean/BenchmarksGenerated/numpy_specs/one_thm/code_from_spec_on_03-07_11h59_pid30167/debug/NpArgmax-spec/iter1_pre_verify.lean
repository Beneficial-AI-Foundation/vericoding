namespace NpArgmax

/- LLM HELPER -/
def argmax_aux {n : Nat} (arr : Vector Float n) (best_idx : Fin n) (curr_idx : Fin n) : Fin n :=
  if h : curr_idx.val < n then
    if arr[curr_idx] > arr[best_idx] then
      argmax_aux arr curr_idx ⟨curr_idx.val + 1, Nat.succ_lt_of_lt h⟩
    else
      argmax_aux arr best_idx ⟨curr_idx.val + 1, Nat.succ_lt_of_lt h⟩
  else
    best_idx

def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  argmax_aux arr ⟨0, h⟩ ⟨0, h⟩

/- LLM HELPER -/
lemma argmax_aux_bounds {n : Nat} (arr : Vector Float n) (best_idx curr_idx : Fin n) :
  (argmax_aux arr best_idx curr_idx).val < n := by
  sorry

/- LLM HELPER -/
lemma argmax_aux_maximizes {n : Nat} (arr : Vector Float n) (best_idx curr_idx : Fin n) :
  ∀ i : Fin n, i.val < curr_idx.val → arr[argmax_aux arr best_idx curr_idx] ≥ arr[i] := by
  sorry

theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i]
  ∧
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i]
  := by
  constructor
  · intro i hi
    sorry
  · intro i hi
    sorry

end NpArgmax