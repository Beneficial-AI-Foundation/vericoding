def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  lst.length > 0 →
  result.length = lst.length ∧
  (∀ i, i < result.length →
    result[i]?.getD 0 ∈ lst ∧
    lst[i]?.getD 0 ∈ result ∧
    result.count (lst[i]?.getD 0) = lst.count (lst[i]?.getD 0)) ∧
  ((lst.head! + lst.getLast?.getD 0) % 2 = 1 →
    result.Sorted Nat.le) ∧
  ((lst.head! + lst.getLast?.getD 0) % 2 = 0 →
    result.Sorted (fun a b => a ≥ b))
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List Nat) : List Nat := 
  if lst.length = 0 then []
  else if (lst.head! + lst.getLast?.getD 0) % 2 = 1 then
    lst.mergeSort
  else
    lst.mergeSort.reverse

-- LLM HELPER
lemma list_empty_length_zero (lst: List Nat) : lst.length = 0 ↔ lst = [] := by
  constructor
  · intro h
    cases lst with
    | nil => rfl
    | cons head tail => simp at h
  · intro h
    simp [h]

-- LLM HELPER
lemma mergeSort_length (lst: List Nat) : lst.mergeSort.length = lst.length := by
  simp [List.length_mergeSort]

-- LLM HELPER
lemma reverse_length (lst: List Nat) : lst.reverse.length = lst.length := by
  simp [List.length_reverse]

-- LLM HELPER
lemma mergeSort_mem (lst: List Nat) (x: Nat) : x ∈ lst.mergeSort ↔ x ∈ lst := by
  simp [List.mem_mergeSort]

-- LLM HELPER
lemma reverse_mem (lst: List Nat) (x: Nat) : x ∈ lst.reverse ↔ x ∈ lst := by
  simp [List.mem_reverse]

-- LLM HELPER
lemma mergeSort_count (lst: List Nat) (x: Nat) : lst.mergeSort.count x = lst.count x := by
  simp [List.count_mergeSort]

-- LLM HELPER
lemma reverse_count (lst: List Nat) (x: Nat) : lst.reverse.count x = lst.count x := by
  simp [List.count_reverse]

-- LLM HELPER
lemma mergeSort_sorted (lst: List Nat) : lst.mergeSort.Sorted Nat.le := by
  simp [List.sorted_mergeSort]

-- LLM HELPER
lemma reverse_sorted_ge (lst: List Nat) : lst.Sorted Nat.le → lst.reverse.Sorted (fun a b => a ≥ b) := by
  intro h
  simp [List.sorted_reverse_iff]
  exact h

-- LLM HELPER
lemma nat_mod_two_cases (n: Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have h := Nat.mod_two_eq_zero_or_one n
  cases h with
  | inl h => left; exact h
  | inr h => right; exact h

theorem correctness
(lst: List Nat) : problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro h_len_pos
    simp [implementation]
    split_ifs with h_empty h_odd
    · simp [list_empty_length_zero] at h_empty
      simp [h_empty] at h_len_pos
    · constructor
      · simp [mergeSort_length]
      · constructor
        · intro i h_i
          constructor
          · simp [mergeSort_mem]
          · constructor
            · simp [mergeSort_mem]
            · simp [mergeSort_count]
        · constructor
          · intro h_mod_one
            simp [mergeSort_sorted]
          · intro h_mod_zero
            have h_not_one : ¬((lst.head! + lst.getLast?.getD 0) % 2 = 1) := by
              have h_cases := nat_mod_two_cases (lst.head! + lst.getLast?.getD 0)
              cases h_cases with
              | inl h_zero => simp [h_zero, h_mod_zero]
              | inr h_one => simp [h_one] at h_mod_zero
            simp [h_not_one] at h_odd
            contradiction
    · constructor
      · simp [reverse_length, mergeSort_length]
      · constructor
        · intro i h_i
          constructor
          · simp [reverse_mem, mergeSort_mem]
          · constructor
            · simp [reverse_mem, mergeSort_mem]
            · simp [reverse_count, mergeSort_count]
        · constructor
          · intro h_mod_one
            simp [h_mod_one] at h_odd
          · intro h_mod_zero
            apply reverse_sorted_ge
            exact mergeSort_sorted lst