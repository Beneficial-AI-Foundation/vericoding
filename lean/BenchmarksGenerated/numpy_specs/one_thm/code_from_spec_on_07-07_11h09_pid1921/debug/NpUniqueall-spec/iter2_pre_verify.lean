namespace NpUniqueall

-- LLM HELPER
def unique_all_aux (acc : List Int) (remaining : List Int) : List Int :=
  match remaining with
  | [] => acc.reverse
  | x :: xs => 
    if acc.contains x then
      unique_all_aux acc xs
    else
      unique_all_aux (x :: acc) xs

def unique_all {n : Nat} (arr : Vector Int n) : Vector Int n :=
  let unique_list := unique_all_aux [] arr.toList
  ⟨unique_list, by simp [Vector.length_toList]⟩

-- LLM HELPER
lemma unique_all_aux_preserves_elements (acc : List Int) (remaining : List Int) :
  ∀ x ∈ remaining, x ∈ unique_all_aux acc remaining ∨ x ∈ acc := by
  intro x hx
  induction remaining generalizing acc with
  | nil => simp at hx
  | cons y ys ih =>
    simp [unique_all_aux]
    cases' List.mem_cons.mp hx with h h
    · -- x = y case
      subst h
      by_cases hy : acc.contains y
      · right; exact List.mem_of_mem_contains hy
      · left; apply ih; simp
    · -- x ∈ ys case
      by_cases hy : acc.contains y
      · exact ih h
      · cases' ih (y :: acc) h with h1 h2
        · left; exact h1
        · right; cases' h2 with h3 h4
          · exact h4
          · exact h4

-- LLM HELPER
lemma unique_all_aux_no_duplicates (acc : List Int) (remaining : List Int) 
  (h_acc : acc.Nodup) : (unique_all_aux acc remaining).Nodup := by
  induction remaining generalizing acc with
  | nil => simp [unique_all_aux]; exact h_acc.reverse
  | cons y ys ih =>
    simp [unique_all_aux]
    by_cases hy : acc.contains y
    · exact ih h_acc
    · apply ih
      constructor
      · intro h_mem
        exact hy (List.mem_contains_of_mem h_mem)
      · exact h_acc

-- LLM HELPER
lemma unique_all_aux_length_le (acc : List Int) (remaining : List Int) :
  (unique_all_aux acc remaining).length ≤ acc.length + remaining.length := by
  induction remaining generalizing acc with
  | nil => simp [unique_all_aux]
  | cons y ys ih =>
    simp [unique_all_aux]
    by_cases hy : acc.contains y
    · have h := ih acc
      omega
    · have h := ih (y :: acc)
      simp at h
      omega

theorem unique_all_spec {n : Nat} (arr : Vector Int n) :
  let ret := unique_all arr
  (ret.toList.length ≤ n) ∧
  (∀ i : Fin n, ∃ j : Nat, j < ret.toList.length ∧ ret[j]! = arr[i]) ∧
  (∀ i j : Nat, i < ret.toList.length → j < i → ret[i]! ≠ ret[j]!) := by
  simp [unique_all]
  constructor
  · -- Length constraint
    have h := unique_all_aux_length_le [] arr.toList
    simp at h
    rw [Vector.length_toList] at h
    exact h
  constructor
  · -- All elements preserved
    intro i
    have h := unique_all_aux_preserves_elements [] arr.toList (arr[i])
    simp at h
    have mem : arr[i] ∈ arr.toList := by
      rw [Vector.mem_toList_iff]
      use i
    have h_elem := h mem
    cases' h_elem with h1 h2
    · -- Element is in the result
      rw [List.mem_iff_get] at h1
      obtain ⟨j, hj⟩ := h1
      use j.val
      constructor
      · exact j.isLt
      · simp [Vector.getElem_mk]
        rw [List.get_reverse]
        simp
        exact hj.symm
    · -- Element is in empty acc (impossible)
      simp at h2
  · -- No duplicates
    intro i j hi hj
    have h_nodup := unique_all_aux_no_duplicates [] arr.toList (by simp)
    simp [Vector.getElem_mk] at h_nodup ⊢
    have h_get_ne := List.nodup_iff_get_ne_get.mp h_nodup
    apply h_get_ne
    · exact hi
    · exact hj
    · omega

end NpUniqueall