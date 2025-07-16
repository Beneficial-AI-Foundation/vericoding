def problem_spec
(implementation: List Int → Int → List Int)
(arr: List Int)
(k: Int) :=
let spec (result: List Int) :=
    1 ≤ arr.length → arr.length ≤ 1000 → arr.all (fun x => -1000 ≤ x ∧ x ≤ 1000) → 0 ≤ k → k ≤ arr.length →
    result.length = k ∧
    List.Sorted (· ≤ ·) result ∧
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
  else
    match arr.max? with
    | none => []
    | some max => 
      let remaining := arr.erase max
      let rest := implementation remaining (k - 1)
      rest ++ [max]
termination_by arr.length + Int.natAbs k

-- LLM HELPER
lemma max_in_list (arr: List Int) (max: Int) : arr.max? = some max → max ∈ arr := by
  intro h
  exact List.max?_mem h

-- LLM HELPER
lemma erase_length_lt (arr: List Int) (x: Int) : x ∈ arr → (arr.erase x).length < arr.length := by
  exact List.length_erase_of_mem

-- LLM HELPER
lemma sorted_append_max (l: List Int) (max: Int) : List.Sorted (· ≤ ·) l → (∀ x ∈ l, x ≤ max) → List.Sorted (· ≤ ·) (l ++ [max]) := by
  intro h_sorted h_max
  exact List.sorted_append.mpr ⟨h_sorted, List.sorted_singleton max, fun _ _ h_mem => h_max _ (List.mem_of_mem_head? h_mem)⟩

-- LLM HELPER
lemma mem_of_mem_erase (arr: List Int) (x y: Int) : x ∈ arr.erase y → x ∈ arr := by
  exact List.mem_of_mem_erase

-- LLM HELPER
lemma all_le_max (arr: List Int) (max: Int) : arr.max? = some max → ∀ x ∈ arr, x ≤ max := by
  intro h x hx
  exact List.le_max_of_mem hx h

-- LLM HELPER
lemma implementation_length (arr: List Int) (k: Int) : 
  0 ≤ k → k ≤ arr.length → (implementation arr k).length = Int.natAbs k := by
  intro h_k_nonneg h_k_le
  induction' k using Int.induction_on generalizing arr with
  | hz =>
    simp [implementation, Int.natAbs]
  | hp n h_nonneg ih =>
    simp [implementation]
    if h_pos : n + 1 ≤ 0 then
      simp [h_pos]
      simp [Int.natAbs] at h_pos
    else
      simp [h_pos]
      cases' h_max : arr.max? with max
      · simp
        have h_empty : arr = [] := by
          cases arr with
          | nil => rfl
          | cons a l => simp [List.max?] at h_max
        rw [h_empty] at h_k_le
        simp at h_k_le
        have : n + 1 ≤ 0 := by omega
        contradiction
      · simp
        have h_mem : max ∈ arr := max_in_list arr max h_max
        have h_erase_len : (arr.erase max).length < arr.length := erase_length_lt arr max h_mem
        have h_erase_len_le : (arr.erase max).length ≤ arr.length - 1 := by
          rw [← Nat.cast_le (α := Int)]
          simp
          exact Nat.le_sub_one_of_lt h_erase_len
        have h_n_le : n ≤ (arr.erase max).length := by omega
        have h_n_nonneg : 0 ≤ n := by omega
        rw [ih h_n_nonneg h_n_le]
        simp [Int.natAbs]
        omega
  | hn n h_neg =>
    have : k ≤ 0 := by omega
    simp [implementation, this]
    simp [Int.natAbs]
    omega

-- LLM HELPER
lemma implementation_all_mem (arr: List Int) (k: Int) : 
  ∀ x ∈ implementation arr k, x ∈ arr := by
  intro x h_mem
  induction' k using Int.induction_on generalizing arr with
  | hz =>
    simp [implementation] at h_mem
  | hp n h_nonneg ih =>
    simp [implementation] at h_mem
    if h_pos : n + 1 ≤ 0 then
      simp [h_pos] at h_mem
    else
      simp [h_pos] at h_mem
      cases' h_max : arr.max? with max
      · simp at h_mem
      · simp at h_mem
        cases h_mem with
        | inl h_left =>
          have h_mem_erase : x ∈ arr.erase max := by
            exact ih _ h_left
          exact mem_of_mem_erase arr x max h_mem_erase
        | inr h_right =>
          simp at h_right
          rw [h_right]
          exact max_in_list arr max h_max
  | hn n h_neg =>
    simp [implementation] at h_mem

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k := by
  unfold problem_spec
  use implementation arr k
  constructor
  · rfl
  · intro h_len_ge h_len_le h_bounded h_k_ge h_k_le
    constructor
    · -- result.length = k
      have h_eq : (implementation arr k).length = Int.natAbs k := implementation_length arr k h_k_ge h_k_le
      rw [h_eq]
      simp [Int.natAbs]
      omega
    constructor
    · -- result.Sorted (· ≤ ·)
      induction' k using Int.induction_on generalizing arr with
      | hz =>
        simp [implementation]
        exact List.sorted_nil
      | hp n h_nonneg ih =>
        simp [implementation]
        if h_pos : n + 1 ≤ 0 then
          simp [h_pos]
          exact List.sorted_nil
        else
          simp [h_pos]
          cases' h_max : arr.max? with max
          · simp
            exact List.sorted_nil
          · simp
            have h_mem : max ∈ arr := max_in_list arr max h_max
            have h_erase_len : (arr.erase max).length < arr.length := erase_length_lt arr max h_mem
            have h_n_le : n ≤ (arr.erase max).length := by omega
            have h_n_nonneg : 0 ≤ n := by omega
            have h_sorted_rest : List.Sorted (· ≤ ·) (implementation (arr.erase max) n) := by
              exact ih _ h_n_nonneg h_n_le
            have h_all_le : ∀ x ∈ implementation (arr.erase max) n, x ≤ max := by
              intro x h_mem_x
              have h_mem_erase : x ∈ arr.erase max := implementation_all_mem (arr.erase max) n x h_mem_x
              have h_mem_arr : x ∈ arr := mem_of_mem_erase arr x max h_mem_erase
              exact all_le_max arr max h_max x h_mem_arr
            exact sorted_append_max (implementation (arr.erase max) n) max h_sorted_rest h_all_le
      | hn n h_neg =>
        simp [implementation]
        exact List.sorted_nil
    constructor
    · -- ∀ x ∈ result, x ∈ arr
      exact implementation_all_mem arr k
    · -- recursive property
      if h_zero : k = 0 then
        simp [h_zero, implementation]
      else
        simp [implementation]
        if h_nonpos : k ≤ 0 then
          have : k = 0 := by omega
          contradiction
        else
          simp [h_nonpos]
          cases' h_max : arr.max? with max
          · simp
            have h_empty : arr = [] := by
              cases arr with
              | nil => rfl
              | cons a l => simp [List.max?] at h_max
            rw [h_empty] at h_len_ge
            simp at h_len_ge
          · simp
            constructor
            · exact h_max
            · simp [List.reverse_append, List.reverse_cons, List.reverse_nil]
              rfl