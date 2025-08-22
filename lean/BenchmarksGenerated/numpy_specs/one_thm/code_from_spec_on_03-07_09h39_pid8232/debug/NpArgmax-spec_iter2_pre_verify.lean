namespace NpArgmax

/- LLM HELPER -/
def argmax_aux {n : Nat} (arr : Vector Float n) (current_max_idx : Fin n) (k : Fin n) : Fin n :=
  if arr[k] > arr[current_max_idx] then k else current_max_idx

def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n :=
  let first_idx : Fin n := ⟨0, h⟩
  match n with
  | 0 => False.elim (Nat.lt_irrefl 0 h)
  | m + 1 => 
    let rec find_max (current_idx : Fin (m + 1)) (remaining : Nat) : Fin (m + 1) :=
      match remaining with
      | 0 => current_idx
      | k + 1 => 
        let next_pos := current_idx.val + 1
        if h_next : next_pos < m + 1 then
          let next_idx : Fin (m + 1) := ⟨next_pos, h_next⟩
          let better_idx := if arr[next_idx] > arr[current_idx] then next_idx else current_idx
          find_max better_idx k
        else
          current_idx
    find_max first_idx m

theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i]
  ∧
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i]
  := by
  constructor
  · intro i hi
    simp [argmax] at hi ⊢
    match n with
    | 0 => exact False.elim (Nat.lt_irrefl 0 h)
    | m + 1 => 
      have : i.val < (⟨0, h⟩ : Fin (m + 1)).val := by
        simp at hi
        exact hi
      simp at this
      exact False.elim (Nat.not_lt_zero i.val this)
  · intro i hi
    simp [argmax] at hi ⊢
    match n with
    | 0 => exact False.elim (Nat.lt_irrefl 0 h)
    | m + 1 =>
      have : (⟨0, h⟩ : Fin (m + 1)).val < i.val := by
        simp at hi
        exact hi
      simp at this
      le_refl _

end NpArgmax