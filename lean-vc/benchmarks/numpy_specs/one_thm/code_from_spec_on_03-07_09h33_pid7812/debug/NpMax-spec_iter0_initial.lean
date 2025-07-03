namespace NpMax

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.foldl Int.max (a[0])

/-- LLM HELPER -/
lemma foldl_max_mem {l : List Int} (x : Int) : 
  x ∈ l → x ≤ l.foldl Int.max x := by
  intro h_mem
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp [List.foldl]
    cases h_mem with
    | head => simp [Int.le_max_left]
    | tail h_tail =>
      have : x ≤ tl.foldl Int.max (Int.max x hd) := ih h_tail
      exact le_trans this (Int.le_max_right _ _)

/-- LLM HELPER -/
lemma foldl_max_ge {l : List Int} (x : Int) : 
  x ≤ l.foldl Int.max x := by
  induction l with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    exact le_trans (Int.le_max_left x hd) ih

/-- LLM HELPER -/
lemma foldl_max_in_list {l : List Int} (x : Int) : 
  l ≠ [] → (l.foldl Int.max x = x ∨ l.foldl Int.max x ∈ l) := by
  intro h_ne_nil
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp [List.foldl]
    by_cases h : tl = []
    · simp [h, List.foldl]
      right
      simp [Int.max_def]
      split_ifs <;> simp
    · have := ih h
      cases this with
      | inl h_eq => 
        simp [h_eq]
        right
        simp [Int.max_def]
        split_ifs <;> simp
      | inr h_mem =>
        right
        exact List.mem_cons_of_mem hd h_mem

/-- LLM HELPER -/
lemma vector_get_mem_toList {n : Nat} (a : Vector Int n) (i : Fin n) : 
  a[i] ∈ a.toList := by
  simp [Vector.get_mem_toList]

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  constructor
  · -- Show existence of index
    have h_len : a.toList.length = n := by simp [Vector.toList_length]
    have h_ne_nil : a.toList ≠ [] := by
      intro h_nil
      have : a.toList.length = 0 := by simp [h_nil]
      rw [h_len] at this
      exact Nat.not_eq_zero_of_zero_lt_right h this
    
    simp [max]
    have := foldl_max_in_list (a[0]) h_ne_nil
    cases this with
    | inl h_eq => 
      use 0
      exact h_eq.symm
    | inr h_mem =>
      have : ∃ i : Fin n, a[i] = a.toList.foldl Int.max (a[0]) := by
        rw [Vector.toList_length] at h_len
        have : ∃ i : Fin n, a[i] ∈ a.toList ∧ a[i] = a.toList.foldl Int.max (a[0]) := by
          simp [Vector.mem_toList_iff] at h_mem
          exact ⟨h_mem.1, h_mem.2⟩
        exact ⟨this.1, this.2.2⟩
      exact ⟨this.1, this.2.symm⟩
  
  · -- Show all elements are ≤ max
    intro i
    simp [max]
    have h_mem : a[i] ∈ a.toList := vector_get_mem_toList a i
    exact foldl_max_mem (a[0]) h_mem

end NpMax