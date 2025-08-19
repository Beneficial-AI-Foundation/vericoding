def problem_spec
(implementation: Rat → Rat → Rat → Bool)
(a: Rat) (b: Rat) (c: Rat) :=
let spec (result : Bool) :=
  let nums := [a, b, c];
  result = true ↔ ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ a.den = b.den ∧ a.den = c.den
∃ result,
  implementation a b c = result ∧
  spec result

-- LLM HELPER
def isInteger (r : Rat) : Bool := r.den = 1

-- LLM HELPER
def checkTripleSumProperty (a b c : Rat) : Bool :=
  (a + b = c) ∨ (a + c = b) ∨ (b + c = a)

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  isInteger a ∧ isInteger b ∧ isInteger c ∧ checkTripleSumProperty a b c

-- LLM HELPER
lemma three_distinct_indices : ∀ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i → 
  ({i, j, k} = {0, 1, 2}) := by
  intro i j k h
  have hi : i ∈ ({0, 1, 2} : Set ℕ) := h.1 (Set.mem_insert _ _)
  have hj : j ∈ ({0, 1, 2} : Set ℕ) := h.1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hk : k ∈ ({0, 1, 2} : Set ℕ) := h.1 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  -- Since we have 3 distinct elements from a 3-element set, they must be equal
  have card_ijk : Set.ncard {i, j, k} = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨i, j, k, h.2.1, h.2.2.1, h.2.2.2, rfl⟩
  have card_012 : Set.ncard ({0, 1, 2} : Set ℕ) = 3 := by 
    simp [Set.ncard_insert_of_not_mem]
    norm_num
  have sub : {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) := h.1
  have eq_card : Set.ncard {i, j, k} = Set.ncard ({0, 1, 2} : Set ℕ) := by rw [card_ijk, card_012]
  exact Set.eq_of_subset_of_ncard_eq sub eq_card

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp [problem_spec, implementation, isInteger, checkTripleSumProperty]
  use (a.den = 1 ∧ b.den = 1 ∧ c.den = 1 ∧ ((a + b = c) ∨ (a + c = b) ∨ (b + c = a)))
  constructor
  · rfl
  · constructor
    · intro h
      cases' h with h_int h_sum
      cases' h_int with h_a h_rest  
      cases' h_rest with h_b h_c
      cases' h_sum with h1 h_sum
      · -- case a + b = c
        use 0, 1, 2
        constructor
        · simp [Set.subset_def]
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · simp [List.get!, h1]
        exact ⟨h_a, h_b, h_c⟩
      cases' h_sum with h2 h3
      · -- case a + c = b
        use 0, 2, 1
        constructor
        · simp [Set.subset_def]
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · simp [List.get!, h2]
        exact ⟨h_a, h_b, h_c⟩
      · -- case b + c = a
        use 1, 2, 0
        constructor
        · simp [Set.subset_def]
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · simp [List.get!, h3]
        exact ⟨h_a, h_b, h_c⟩
    · intro h_exists
      cases' h_exists with i h_i
      cases' h_i with j h_j
      cases' h_j with k h_k
      have h_eq := three_distinct_indices i j k ⟨h_k.1, h_k.2.1, h_k.2.2.1, h_k.2.2.2.1⟩
      constructor
      · exact h_k.2.2.2.2.1
      constructor
      · rw [h_k.2.2.2.2.2.1]; exact h_k.2.2.2.2.2.2
      constructor
      · rw [h_k.2.2.2.2.2.1]; exact h_k.2.2.2.2.2.2
      -- Now we need to show one of the sum conditions
      have sum_eq : [a, b, c][i]! + [a, b, c][j]! = [a, b, c][k]! := h_k.2.2.2.1
      -- Since {i,j,k} = {0,1,2} and all are distinct, we have three cases
      have hi_mem : i ∈ ({0, 1, 2} : Set ℕ) := h_k.1 (Set.mem_insert _ _)
      have hj_mem : j ∈ ({0, 1, 2} : Set ℕ) := h_k.1 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      have hk_mem : k ∈ ({0, 1, 2} : Set ℕ) := h_k.1 (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      interval_cases i <;> interval_cases j <;> interval_cases k <;>
      (try simp at h_k.2.1 h_k.2.2.1 h_k.2.2.2.1) <;>
      (try (left; simp [List.get!] at sum_eq; exact sum_eq)) <;>
      (try (right; left; simp [List.get!] at sum_eq; exact sum_eq)) <;>
      (try (right; right; simp [List.get!] at sum_eq; exact sum_eq))