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
      omega
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
      have : maxIdx.val = 0 := by
        have : maxIdx.val < n := maxIdx.isLt
        have : 0 < n := by omega
        omega
      exact this
    simp [this]
  | succ k ih =>
    intro i hi
    simp [findMaxIndexAux]
    have h : k < n := by omega
    let j := ⟨k, h⟩
    have prop := findMaxIndex_property arr maxIdx j
    have : arr[findMaxIndex arr maxIdx j] ≥ arr[maxIdx] := prop.1
    by_cases h_eq : i.val = k + 1
    · have : arr[findMaxIndex arr maxIdx j] ≥ arr[j] := prop.2
      have : j = i := by
        ext
        simp [j]
        omega
      simp [this] at this
      exact this
    · have : i.val ≤ k := by omega
      exact ih i this

theorem argmax_spec {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i]
  ∧
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i]
  := by
  intro i
  unfold argmax
  have h_pos : 0 < n := h
  have h_bound : n - 1 < n := Nat.sub_lt h_pos (by norm_num)
  let result := findMaxIndexAux arr (n-1) ⟨0, h⟩
  have max_prop : ∀ j : Fin n, j.val ≤ n-1 → arr[result] ≥ arr[j] := by
    apply findMaxIndexAux_is_max
  have all_covered : ∀ j : Fin n, j.val ≤ n-1 := by
    intro j
    have : j.val < n := j.isLt
    omega
  and_iff_right.mpr (fun hi => max_prop i (all_covered i))

end NpArgmax