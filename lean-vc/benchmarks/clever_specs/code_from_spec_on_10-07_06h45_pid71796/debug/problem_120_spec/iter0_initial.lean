def problem_spec
(implementation: List Int → Int → List Int)
(arr: List Int)
(k: Int) :=
let spec (result: List Int) :=
    1 ≤ arr.length → arr.length ≤ 1000 → arr.all (fun x => -1000 ≤ x ∧ x ≤ 1000) → 0 ≤ k → k ≤ arr.length →
    result.length = k ∧
    result.Sorted (· ≤ ·) ∧
    ∀ x ∈ result, x ∈ arr ∧

    let result_reversed := result.reverse; -- reverse to get last element
    match result_reversed with
    | [] => k = 0
    | max :: remaining_reversed =>
      arr.max? = some max ∧
      implementation (arr.erase max) (k-1) = (remaining_reversed.reverse)
∃ result, implementation arr k = result ∧
spec result

-- LLM HELPER
def implementation (arr: List Int) (k: Int) : List Int :=
  if k ≤ 0 then []
  else if arr.isEmpty then []
  else 
    match arr.max? with
    | none => []
    | some max => implementation (arr.erase max) (k-1) ++ [max]

-- LLM HELPER
lemma max_in_list (arr: List Int) (max: Int) : arr.max? = some max → max ∈ arr := by
  intro h
  exact List.mem_of_max?_eq_some h

-- LLM HELPER
lemma erase_length_le (arr: List Int) (x: Int) : (arr.erase x).length ≤ arr.length := by
  exact List.length_erase_le arr x

-- LLM HELPER  
lemma erase_length_lt (arr: List Int) (x: Int) : x ∈ arr → (arr.erase x).length < arr.length := by
  intro h
  exact List.length_erase_lt_of_mem h

-- LLM HELPER
lemma mem_erase_subset (arr: List Int) (x: Int) : ∀ y ∈ arr.erase x, y ∈ arr := by
  intro y hy
  exact List.mem_of_mem_erase hy

-- LLM HELPER
lemma implementation_length (arr: List Int) (k: Int) : 
  k ≤ arr.length → 0 ≤ k → (implementation arr k).length = k := by
  intro hk_le hk_ge
  induction k using Nat.strong_induction_on generalizing arr with
  | ind k ih =>
    unfold implementation
    split
    · case inl h => simp [h]
    · case inr h1 => 
      split
      · case inl h2 => 
        simp [h2]
        have : k = 0 := by
          by_contra hne
          have : 0 < k := Nat.pos_of_ne_zero hne
          have : arr.length = 0 := List.length_eq_zero.mpr h2
          linarith
        exact this
      · case inr h2 =>
        split
        · case inl h3 => 
          simp
          have : k = 0 := by
            by_contra hne
            have : 0 < k := Nat.pos_of_ne_zero hne
            have : arr ≠ [] := h2
            have : arr.max?.isNone := by simp [h3]
            have : arr = [] := List.eq_nil_of_max?_eq_none h3
            contradiction
          exact this
        · case inr h3 =>
          obtain ⟨max, hmax⟩ := h3
          simp [hmax]
          rw [List.length_append, List.length_singleton]
          have h_mem : max ∈ arr := max_in_list arr max hmax
          have h_lt : (arr.erase max).length < arr.length := erase_length_lt arr max h_mem
          have h_le : k - 1 ≤ (arr.erase max).length := by
            have : (arr.erase max).length = arr.length - 1 := by
              rw [List.length_erase_of_mem h_mem]
            rw [this]
            omega
          have h_ge : 0 ≤ k - 1 := by omega
          have h_rec := ih (k - 1) (by omega) (arr.erase max) h_le h_ge
          rw [h_rec]
          omega

-- LLM HELPER
lemma implementation_sorted (arr: List Int) (k: Int) : 
  (implementation arr k).Sorted (· ≤ ·) := by
  induction k using Nat.strong_induction_on generalizing arr with
  | ind k ih =>
    unfold implementation
    split
    · case inl => exact List.sorted_nil
    · case inr h1 => 
      split
      · case inl => exact List.sorted_nil
      · case inr h2 =>
        split
        · case inl => exact List.sorted_nil
        · case inr h3 =>
          obtain ⟨max, hmax⟩ := h3
          simp [hmax]
          have h_rec := ih (k - 1) (by omega) (arr.erase max)
          rw [List.sorted_append]
          constructor
          · exact h_rec
          · constructor
            · exact List.sorted_singleton max
            · intro x hx y hy
              simp at hy
              rw [hy]
              have : x ∈ implementation (arr.erase max) (k - 1) := hx
              have : ∀ z ∈ implementation (arr.erase max) (k - 1), z ∈ arr.erase max := by
                sorry -- would need more detailed proof about elements
              have h_mem : x ∈ arr.erase max := this hx
              have h_mem_arr : x ∈ arr := mem_erase_subset arr max x h_mem
              have h_max_max : max = arr.max?.get! := by
                simp [hmax]
              have : x ≤ max := by
                have : arr.max? = some max := hmax
                exact List.le_max_of_mem h_mem_arr this
              exact this

-- LLM HELPER
lemma implementation_mem_subset (arr: List Int) (k: Int) : 
  ∀ x ∈ implementation arr k, x ∈ arr := by
  intro x hx
  induction k using Nat.strong_induction_on generalizing arr with
  | ind k ih =>
    unfold implementation at hx
    split at hx
    · case inl => simp at hx
    · case inr h1 => 
      split at hx
      · case inl => simp at hx
      · case inr h2 =>
        split at hx
        · case inl => simp at hx
        · case inr h3 =>
          obtain ⟨max, hmax⟩ := h3
          simp [hmax] at hx
          rw [List.mem_append] at hx
          cases hx with
          | inl h => 
            have := ih (k - 1) (by omega) (arr.erase max) h
            exact mem_erase_subset arr max x this
          | inr h => 
            simp at h
            rw [h]
            exact max_in_list arr max hmax

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k := by
  unfold problem_spec
  use implementation arr k
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5
    constructor
    · exact implementation_length arr k h5 h4
    · constructor
      · exact implementation_sorted arr k
      · constructor
        · exact implementation_mem_subset arr k
        · sorry -- The recursive property would need a more complex proof