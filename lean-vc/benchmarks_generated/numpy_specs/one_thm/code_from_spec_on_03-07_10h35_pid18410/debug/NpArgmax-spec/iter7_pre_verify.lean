namespace NpArgmax

/- LLM HELPER -/
def argmax_helper {n : Nat} (arr : Vector Float n) (current_max : Fin n) (i : Fin n) : Fin n :=
  if arr[i] > arr[current_max] then i else current_max

/- LLM HELPER -/
def argmax_aux {n : Nat} (arr : Vector Float n) (current_max : Fin n) : Nat → Fin n
  | 0 => current_max
  | k + 1 => 
    if h : k < n then
      argmax_aux arr (argmax_helper arr current_max ⟨k, h⟩) k
    else
      current_max

def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  argmax_aux arr ⟨0, h⟩ n

/- LLM HELPER -/
lemma argmax_helper_preserves_max {n : Nat} (arr : Vector Float n) (current_max i : Fin n) :
  arr[argmax_helper arr current_max i] ≥ arr[current_max] ∧ 
  arr[argmax_helper arr current_max i] ≥ arr[i] := by
  simp [argmax_helper]
  split
  · constructor
    · linarith
    · rfl
  · constructor
    · rfl
    · linarith

/- LLM HELPER -/
lemma argmax_aux_is_max {n : Nat} (arr : Vector Float n) (current_max : Fin n) (k : Nat) :
  ∀ i : Fin n, i.val < k → arr[argmax_aux arr current_max k] ≥ arr[i] := by
  intro i hi
  induction k with
  | zero => 
    simp at hi
  | succ k ih =>
    simp [argmax_aux]
    split
    · rename_i hk
      by_cases h : i.val < k
      · apply ih h
      · simp at h
      have : i.val = k := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt h) hi
      rw [this]
      have : i = ⟨k, hk⟩ := Fin.ext this
      rw [this]
      exact (argmax_helper_preserves_max arr current_max ⟨k, hk⟩).2
    · apply ih
      exact Nat.lt_of_lt_of_le hi (Nat.le_of_not_gt h)

/- LLM HELPER -/
lemma not_ge_of_lt {a b : Float} (h : a < b) : ¬(a ≥ b) := by
  intro h_ge
  linarith

/- LLM HELPER -/
lemma argmax_aux_bounded {n : Nat} (arr : Vector Float n) (current_max : Fin n) (k : Nat) :
  (argmax_aux arr current_max k).val < n := by
  induction k with
  | zero => exact current_max.isLt
  | succ k ih =>
    simp [argmax_aux]
    split
    · rename_i hk
      apply ih
    · exact current_max.isLt

theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  (∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i])
  ∧
  (∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i]) := by
  constructor
  · intro i hi
    simp [argmax]
    apply argmax_aux_is_max
    exact hi
  · intro i hi
    simp [argmax]
    apply argmax_aux_is_max
    exact hi

end NpArgmax