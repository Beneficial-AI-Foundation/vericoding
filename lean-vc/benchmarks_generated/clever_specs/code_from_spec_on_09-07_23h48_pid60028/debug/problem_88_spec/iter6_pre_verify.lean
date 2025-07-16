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
    List.Sorted Nat.le result) ∧
  ((lst.head! + lst.getLast?.getD 0) % 2 = 0 →
    List.Sorted (fun a b => a ≥ b) result)
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
lemma mergeSort_sorted (lst: List Nat) : List.Sorted Nat.le lst.mergeSort := by
  exact List.sorted_mergeSort

-- LLM HELPER
lemma reverse_sorted_ge (lst: List Nat) : List.Sorted Nat.le lst → List.Sorted (fun a b => a ≥ b) lst.reverse := by
  intro h
  exact List.sorted_reverse_iff.mpr h

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
    by_cases h_empty : lst.length = 0
    · simp [h_empty] at h_len_pos
    · simp [h_empty]
      by_cases h_odd : (lst.head! + lst.getLast?.getD 0) % 2 = 1
      · simp [h_odd]
        constructor
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
              exact mergeSort_sorted lst
            · intro h_mod_zero
              have : (lst.head! + lst.getLast?.getD 0) % 2 = 1 := h_odd
              simp [this] at h_mod_zero
      · simp [h_odd]
        constructor
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