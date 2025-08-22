namespace NpMax

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.foldl max (a[0])

/-- LLM HELPER -/
def max (x y : Int) : Int := if x ≤ y then y else x

/-- LLM HELPER -/
lemma max_le_left (x y : Int) : x ≤ max x y := by
  simp [max]
  split_ifs <;> simp [le_refl]

/-- LLM HELPER -/
lemma max_le_right (x y : Int) : y ≤ max x y := by
  simp [max]
  split_ifs <;> simp [le_refl]

/-- LLM HELPER -/
lemma foldl_max_mem {l : List Int} (x : Int) : 
  x ∈ l → x ≤ l.foldl max x := by
  intro h_mem
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp [List.foldl]
    cases h_mem with
    | head => simp [max_le_left]
    | tail h_tail =>
      have : x ≤ tl.foldl max (max x hd) := ih h_tail
      exact le_trans this (max_le_right _ _)

/-- LLM HELPER -/
lemma foldl_max_ge {l : List Int} (x : Int) : 
  x ≤ l.foldl max x := by
  induction l with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    exact le_trans (max_le_left x hd) ih

/-- LLM HELPER -/
lemma foldl_max_in_list {l : List Int} (x : Int) : 
  l ≠ [] → (l.foldl max x = x ∨ l.foldl max x ∈ l) := by
  intro h_ne_nil
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp [List.foldl]
    by_cases h : tl = []
    · simp [h, List.foldl]
      right
      simp [max]
      split_ifs <;> simp
    · have := ih h
      cases this with
      | inl h_eq => 
        simp [h_eq]
        right
        simp [max]
        split_ifs <;> simp
      | inr h_mem =>
        right
        exact List.mem_cons_of_mem hd h_mem

/-- LLM HELPER -/
lemma vector_get_mem_toList {n : Nat} (a : Vector Int n) (i : Fin n) : 
  a[i] ∈ a.toList := by
  exact Vector.get_mem_toList a i

/-- LLM HELPER -/
lemma nat_pos_ne_zero {n : Nat} (h : n > 0) : n ≠ 0 := by
  omega

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  constructor
  · -- Show existence of index
    have h_len : a.toList.length = n := Vector.toList_length a
    have h_ne_nil : a.toList ≠ [] := by
      intro h_nil
      have : a.toList.length = 0 := by simp [h_nil]
      rw [h_len] at this
      exact nat_pos_ne_zero h this
    
    simp [max]
    have := foldl_max_in_list (a[⟨0, Nat.pos_iff_ne_zero.mp h⟩]) h_ne_nil
    cases this with
    | inl h_eq => 
      use ⟨0, Nat.pos_iff_ne_zero.mp h⟩
      exact h_eq.symm
    | inr h_mem =>
      rw [Vector.mem_toList_iff] at h_mem
      exact ⟨h_mem.1, h_mem.2.symm⟩
  
  · -- Show all elements are ≤ max
    intro i
    simp [max]
    have h_mem : a[i] ∈ a.toList := vector_get_mem_toList a i
    exact foldl_max_mem (a[⟨0, Nat.pos_iff_ne_zero.mp h⟩]) h_mem

end NpMax