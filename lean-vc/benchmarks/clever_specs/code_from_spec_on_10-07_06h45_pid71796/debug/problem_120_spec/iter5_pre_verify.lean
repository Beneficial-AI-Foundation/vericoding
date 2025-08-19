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

def implementation (arr: List Int) (k: Int) : List Int :=
  if k ≤ 0 then []
  else if arr.isEmpty then []
  else 
    match arr.max? with
    | none => []
    | some max => implementation (arr.erase max) (k-1) ++ [max]
termination_by k.toNat

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
  induction k using Int.natCast_induction_on generalizing arr with
  | neg => 
    unfold implementation
    simp
    omega
  | zero => 
    unfold implementation
    simp
  | succ n ih =>
    unfold implementation
    simp [Int.succ_pos]
    split
    · simp
    · split
      · simp [List.length_nil]
        omega
      · obtain ⟨max, hmax⟩ := ‹arr.max? = some max›
        simp [hmax]
        rw [List.length_append, List.length_singleton]
        have h_mem : max ∈ arr := max_in_list arr max hmax
        have h_lt : (arr.erase max).length < arr.length := erase_length_lt arr max h_mem
        have h_le : n ≤ (arr.erase max).length := by
          have : (arr.erase max).length = arr.length - 1 := by
            rw [List.length_erase_of_mem h_mem]
          rw [this]
          omega
        have h_ge : 0 ≤ n := by omega
        have h_rec := ih (arr.erase max) h_le h_ge
        rw [h_rec]
        omega

-- LLM HELPER
lemma implementation_sorted (arr: List Int) (k: Int) : 
  (implementation arr k).Sorted (· ≤ ·) := by
  induction k using Int.natCast_induction_on generalizing arr with
  | neg => 
    unfold implementation
    simp
    exact List.sorted_nil
  | zero => 
    unfold implementation
    simp
    exact List.sorted_nil
  | succ n ih =>
    unfold implementation
    simp [Int.succ_pos]
    split
    · exact List.sorted_nil
    · split
      · exact List.sorted_nil
      · obtain ⟨max, hmax⟩ := ‹arr.max? = some max›
        simp [hmax]
        have h_rec := ih (arr.erase max)
        rw [List.sorted_append]
        constructor
        · exact h_rec
        · constructor
          · exact List.sorted_singleton max
          · intro x hx y hy
            simp at hy
            rw [hy]
            have h_mem_erase : x ∈ arr.erase max := by
              have : ∀ z ∈ implementation (arr.erase max) n, z ∈ arr.erase max := by
                exact implementation_mem_subset (arr.erase max) n
              exact this hx
            have h_mem_arr : x ∈ arr := mem_erase_subset arr max x h_mem_erase
            exact List.le_max_of_mem h_mem_arr hmax

-- LLM HELPER
lemma implementation_mem_subset (arr: List Int) (k: Int) : 
  ∀ x ∈ implementation arr k, x ∈ arr := by
  intro x hx
  induction k using Int.natCast_induction_on generalizing arr with
  | neg => 
    unfold implementation at hx
    simp at hx
  | zero => 
    unfold implementation at hx
    simp at hx
  | succ n ih =>
    unfold implementation at hx
    simp [Int.succ_pos] at hx
    split at hx
    · simp at hx
    · split at hx
      · simp at hx
      · obtain ⟨max, hmax⟩ := ‹arr.max? = some max›
        simp [hmax] at hx
        rw [List.mem_append] at hx
        cases hx with
        | inl h => 
          have := ih (arr.erase max) h
          exact mem_erase_subset arr max x this
        | inr h => 
          simp at h
          rw [h]
          exact max_in_list arr max hmax

-- LLM HELPER
lemma implementation_recursive_property (arr: List Int) (k: Int) :
  k > 0 → ¬arr.isEmpty → 
  let result := implementation arr k
  let result_reversed := result.reverse
  match result_reversed with
  | [] => k = 0
  | max :: remaining_reversed =>
    arr.max? = some max ∧
    implementation (arr.erase max) (k-1) = remaining_reversed.reverse := by
  intro hk_pos hne
  unfold implementation
  simp [hk_pos, hne]
  split
  · contradiction
  · obtain ⟨max, hmax⟩ := ‹arr.max? = some max›
    simp [hmax]
    let rec_result := implementation (arr.erase max) (k-1)
    let full_result := rec_result ++ [max]
    have h_rev : full_result.reverse = max :: rec_result.reverse := by
      rw [List.reverse_append, List.reverse_singleton]
    rw [h_rev]
    simp
    constructor
    · exact hmax
    · rw [List.reverse_reverse]

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
        · by_cases hk : k = 0
          · simp [hk]
            unfold implementation
            simp
          · have hk_pos : k > 0 := by omega
            by_cases harr : arr.isEmpty
            · simp [harr]
              unfold implementation
              simp [hk_pos, harr]
              omega
            · exact implementation_recursive_property arr k hk_pos harr