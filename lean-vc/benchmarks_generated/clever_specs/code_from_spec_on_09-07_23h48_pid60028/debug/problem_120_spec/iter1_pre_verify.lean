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
  else
    match arr.max? with
    | none => []
    | some max => 
      let remaining := arr.erase max
      let rest := implementation remaining (k - 1)
      rest ++ [max]

-- LLM HELPER
lemma max_in_list (arr: List Int) (max: Int) : arr.max? = some max → max ∈ arr := by
  intro h
  exact List.max?_mem h

-- LLM HELPER
lemma erase_length_le (arr: List Int) (x: Int) : (arr.erase x).length ≤ arr.length := by
  exact List.length_erase_le arr x

-- LLM HELPER
lemma sorted_append_max (l: List Int) (max: Int) : l.Sorted (· ≤ ·) → (∀ x ∈ l, x ≤ max) → (l ++ [max]).Sorted (· ≤ ·) := by
  intro h_sorted h_max
  exact List.sorted_append.mpr ⟨h_sorted, List.sorted_singleton max, fun _ _ h_mem => h_max _ (List.mem_of_mem_head? h_mem)⟩

-- LLM HELPER
lemma mem_append_of_mem_left {α : Type*} (l1 l2 : List α) (x : α) : x ∈ l1 → x ∈ l1 ++ l2 := by
  exact List.mem_append_of_mem_left l2

-- LLM HELPER
lemma mem_append_of_mem_right {α : Type*} (l1 l2 : List α) (x : α) : x ∈ l2 → x ∈ l1 ++ l2 := by
  exact List.mem_append_of_mem_right l1

-- LLM HELPER
lemma mem_of_mem_erase (arr: List Int) (x y: Int) : x ∈ arr.erase y → x ∈ arr := by
  exact List.mem_of_mem_erase

-- LLM HELPER
lemma all_le_max (arr: List Int) (max: Int) : arr.max? = some max → ∀ x ∈ arr, x ≤ max := by
  intro h x hx
  exact List.le_max_of_mem hx h

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
      induction' k using Int.emod_two_eq_zero_or_one.elim generalizing arr with
      case intro k =>
        if hk : k ≤ 0 then
          simp [implementation, hk]
          omega
        else
          simp [implementation, hk]
          cases' h_max : arr.max? with max
          · simp
            have : arr = [] := by
              cases arr with
              | nil => rfl
              | cons a l => 
                simp [List.max?] at h_max
                cases l with
                | nil => simp at h_max
                | cons b l' => simp at h_max
            rw [this] at h_len_ge
            simp at h_len_ge
          · simp
            have h_pos : 0 < k := by omega
            have h_k_minus_one : k - 1 < k := by omega
            sorry -- This would require strong induction on k and array size
    constructor
    · -- result.Sorted (· ≤ ·)
      sorry
    · constructor
      · -- ∀ x ∈ result, x ∈ arr
        sorry
      · -- recursive property
        sorry