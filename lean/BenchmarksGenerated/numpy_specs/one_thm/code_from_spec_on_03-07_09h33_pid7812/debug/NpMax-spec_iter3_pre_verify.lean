namespace NpMax

/-- LLM HELPER -/
def maxInt (x y : Int) : Int := if x ≤ y then y else x

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.foldl maxInt (a[0])

/-- LLM HELPER -/
lemma maxInt_le_left (x y : Int) : x ≤ maxInt x y := by
  simp [maxInt]
  split_ifs <;> simp [le_refl]

/-- LLM HELPER -/
lemma maxInt_le_right (x y : Int) : y ≤ maxInt x y := by
  simp [maxInt]
  split_ifs <;> simp [le_refl]

/-- LLM HELPER -/
lemma foldl_maxInt_mem {l : List Int} (x : Int) : 
  x ∈ l → x ≤ l.foldl maxInt x := by
  intro h_mem
  induction l generalizing x with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp [List.foldl]
    cases h_mem with
    | head => 
      have : x ≤ maxInt x hd := maxInt_le_left x hd
      have : maxInt x hd ≤ tl.foldl maxInt (maxInt x hd) := by
        induction tl generalizing (maxInt x hd) with
        | nil => simp [List.foldl]
        | cons hd' tl' ih' =>
          simp [List.foldl]
          exact maxInt_le_left _ _
      exact le_trans ‹x ≤ maxInt x hd› this
    | tail h_tail =>
      have : hd ≤ tl.foldl maxInt (maxInt x hd) := ih h_tail
      exact this

/-- LLM HELPER -/
lemma foldl_maxInt_ge {l : List Int} (x : Int) : 
  x ≤ l.foldl maxInt x := by
  induction l generalizing x with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    have : x ≤ maxInt x hd := maxInt_le_left x hd
    have : maxInt x hd ≤ tl.foldl maxInt (maxInt x hd) := ih
    exact le_trans this ‹maxInt x hd ≤ tl.foldl maxInt (maxInt x hd)›

/-- LLM HELPER -/
lemma foldl_maxInt_in_list {l : List Int} (x : Int) : 
  l ≠ [] → (l.foldl maxInt x = x ∨ l.foldl maxInt x ∈ l) := by
  intro h_ne_nil
  induction l generalizing x with
  | nil => contradiction
  | cons hd tl ih =>
    simp [List.foldl]
    by_cases h : tl = []
    · simp [h, List.foldl]
      by_cases h_le : x ≤ hd
      · simp [maxInt, h_le]
        right
        simp
      · simp [maxInt, h_le]
        left
        rfl
    · have := ih h
      cases this with
      | inl h_eq => 
        simp [h_eq]
        by_cases h_le : x ≤ hd
        · simp [maxInt, h_le]
          right
          simp
        · simp [maxInt, h_le]
          left
          rfl
      | inr h_mem =>
        right
        exact List.mem_cons_of_mem hd h_mem

/-- LLM HELPER -/
lemma vector_get_mem_toList {n : Nat} (a : Vector Int n) (i : Fin n) : 
  a[i] ∈ a.toList := by
  rw [Vector.mem_toList_iff]
  exact ⟨i, rfl⟩

/-- LLM HELPER -/
lemma nat_pos_ne_zero {n : Nat} (h : n > 0) : n ≠ 0 := by
  omega

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
      exact nat_pos_ne_zero h this
    
    simp [max]
    have h_pos : 0 < n := h
    have h_fin : (0 : Fin n) = ⟨0, h_pos⟩ := rfl
    have := foldl_maxInt_in_list (a[⟨0, h_pos⟩]) h_ne_nil
    cases this with
    | inl h_eq => 
      use ⟨0, h_pos⟩
      exact h_eq.symm
    | inr h_mem =>
      rw [Vector.mem_toList_iff] at h_mem
      exact ⟨h_mem.1, h_mem.2.symm⟩
  
  · -- Show all elements are ≤ max
    intro i
    simp [max]
    have h_mem : a[i] ∈ a.toList := vector_get_mem_toList a i
    have h_pos : 0 < n := h
    exact foldl_maxInt_mem (a[⟨0, h_pos⟩]) h_mem

end NpMax