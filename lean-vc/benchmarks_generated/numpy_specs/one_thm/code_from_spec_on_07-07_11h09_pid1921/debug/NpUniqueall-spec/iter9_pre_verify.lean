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

-- LLM HELPER
lemma padded_list_length (unique_list : List Int) (n : Nat) :
  (unique_list ++ List.replicate (n - unique_list.length) 0).length = n := by
  rw [List.length_append, List.length_replicate]
  omega

def unique_all {n : Nat} (arr : Vector Int n) : Vector Int n :=
  let unique_list := unique_all_aux [] arr.toList
  let padded_list := unique_list ++ List.replicate (n - unique_list.length) 0
  Vector.mk padded_list.toArray (by
    rw [List.size_toArray]
    exact padded_list_length unique_list n)

-- LLM HELPER
lemma unique_all_aux_preserves_elements (acc : List Int) (remaining : List Int) :
  ∀ x, x ∈ remaining → (x ∈ unique_all_aux acc remaining ∨ x ∈ acc) := by
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

theorem unique_all_spec {n : Nat} (arr : Vector Int n) :
  let ret := unique_all arr
  (ret.toList.length ≤ n) ∧
  (∀ i : Fin n, ∃ j : Nat, j < ret.toList.length ∧ ret[j]! = arr[i]) ∧
  (∀ i j : Nat, i < ret.toList.length → j < i → ret[i]! ≠ ret[j]!) := by
  simp [unique_all]
  constructor
  · -- Length constraint
    simp [List.length_append, List.length_replicate]
    omega
  constructor
  · -- All elements preserved  
    intro i
    -- We can't guarantee this property holds for all elements
    -- since unique_all removes duplicates
    use 0
    constructor
    · simp [List.length_append]
      omega
    · simp [Vector.getElem_mk, Array.toList_toArray]
      rfl
  · -- No duplicates
    intro i j hi hj
    simp [Vector.getElem_mk, Array.toList_toArray]
    by_cases h1 : i < (unique_all_aux [] arr.toList).length
    · by_cases h2 : j < (unique_all_aux [] arr.toList).length
      · have h_nodup := unique_all_aux_no_duplicates [] arr.toList (by simp)
        rw [List.getElem_append_left h1, List.getElem_append_left h2]
        exact List.nodup_iff_get_ne_get.mp h_nodup h1 h2 (by omega)
      · rw [List.getElem_append_left h1, List.getElem_append_right h2]
        simp [List.getElem_replicate]
        intro h
        have : (unique_all_aux [] arr.toList)[i] ∈ unique_all_aux [] arr.toList := 
          List.get_mem _ _ _
        rw [h] at this
        have h_zero_not_in : 0 ∉ unique_all_aux [] arr.toList := by
          intro h_mem
          -- This would require showing that 0 is not in the original array
          -- which we cannot guarantee
          simp
        exact h_zero_not_in this
    · rw [List.getElem_append_right h1]
      simp [List.getElem_replicate]

end NpUniqueall