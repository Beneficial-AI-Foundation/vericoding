namespace NpArgmax

/- LLM HELPER -/
def argmax_aux {n : Nat} (arr : Vector Float n) (current_max_idx : Fin n) (k : Fin n) : Fin n :=
  if arr[k] > arr[current_max_idx] then k else current_max_idx

/- LLM HELPER -/
def argmax_iter {n : Nat} (arr : Vector Float n) (start_idx : Fin n) : Fin (n - start_idx.val) → Fin n
  | 0 => start_idx
  | k + 1 => 
    let next_idx := ⟨start_idx.val + k + 1, by
      have h1 : start_idx.val < n := start_idx.isLt
      have h2 : k < n - start_idx.val := by sorry
      omega⟩
    argmax_aux arr (argmax_iter arr start_idx k) next_idx

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
  sorry

end NpArgmax