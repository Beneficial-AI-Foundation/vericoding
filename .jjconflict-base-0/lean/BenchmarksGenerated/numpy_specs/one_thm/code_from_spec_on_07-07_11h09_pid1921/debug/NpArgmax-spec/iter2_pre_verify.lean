namespace NpArgmax

-- LLM HELPER
def findMaxIndex {n : Nat} (arr : Vector Float n) : Fin n → Fin n → Fin n :=
  fun maxIdx i => if arr[i] > arr[maxIdx] then i else maxIdx

-- LLM HELPER
def findMaxIndexAux {n : Nat} (arr : Vector Float n) : Nat → Fin n → Fin n
  | 0, maxIdx => maxIdx
  | k+1, maxIdx => 
    have h : k < n := by
      have : maxIdx.val < n := maxIdx.isLt
      sorry -- This would require proving k < n from the context
    let i := ⟨k, h⟩
    findMaxIndexAux arr k (findMaxIndex arr maxIdx i)

def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  have h_pos : 0 < n := h
  have h_bound : n - 1 < n := Nat.sub_lt h_pos (by norm_num)
  findMaxIndexAux arr (n-1) ⟨0, h⟩

-- LLM HELPER
lemma findMaxIndex_property {n : Nat} (arr : Vector Float n) (maxIdx i : Fin n) :
  arr[findMaxIndex arr maxIdx i] ≥ arr[maxIdx] ∧ arr[findMaxIndex arr maxIdx i] ≥ arr[i] := by
  unfold findMaxIndex
  by_cases h : arr[i] > arr[maxIdx]
  · simp [h]
    exact ⟨le_of_lt h, le_refl _⟩
  · simp [h]
    exact ⟨le_refl _, le_of_not_gt h⟩

-- LLM HELPER
lemma findMaxIndexAux_is_max {n : Nat} (arr : Vector Float n) (k : Nat) (maxIdx : Fin n) :
  ∀ i : Fin n, i.val ≤ k → arr[findMaxIndexAux arr k maxIdx] ≥ arr[i] := by
  induction k with
  | zero => 
    intro i hi
    simp [findMaxIndexAux]
    have : i.val = 0 := Nat.eq_zero_of_le_zero hi
    have : i = maxIdx := by
      ext
      simp [this]
      sorry
    simp [this]
  | succ k ih =>
    intro i hi
    simp [findMaxIndexAux]
    sorry

theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i]
  ∧
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i]
  := by
  intro i
  constructor
  · intro hi
    unfold argmax
    sorry
  · intro hi
    unfold argmax
    sorry

end NpArgmax