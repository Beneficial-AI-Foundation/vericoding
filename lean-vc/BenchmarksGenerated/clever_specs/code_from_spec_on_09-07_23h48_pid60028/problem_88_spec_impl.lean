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
    List.Sorted (· ≤ ·) result) ∧
  ((lst.head! + lst.getLast?.getD 0) % 2 = 0 →
    List.Sorted (· ≥ ·) result)
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
lemma getElem_option_mem (lst: List Nat) (i: Nat) (h: i < lst.length) : lst[i]?.getD 0 ∈ lst := by
  have : lst[i]? = some (lst[i]) := List.getElem?_eq_some_getElem h
  simp [this]
  exact List.getElem_mem lst i h

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
        · simp [List.length_mergeSort]
        · constructor
          · intro i h_i
            constructor
            · simp [List.mem_mergeSort]
              by_cases h_bound : i < lst.length
              · exact getElem_option_mem lst i h_bound
              · simp [List.getElem?_eq_none_iff] at h_bound
                simp [h_bound]
                exact List.mem_nil_iff.mp (False.elim (h_bound (by simp [List.length_mergeSort] at h_i; exact h_i)))
            · constructor
              · simp [List.mem_mergeSort]
                by_cases h_bound : i < lst.length
                · exact getElem_option_mem lst i h_bound
                · simp [List.getElem?_eq_none_iff] at h_bound
                  simp [h_bound]
                  exact List.mem_nil_iff.mp (False.elim (h_bound (by simp [List.length_mergeSort] at h_i; exact h_i)))
              · simp [List.count_mergeSort, List.length_mergeSort] at h_i
                simp [List.count_mergeSort]
          · constructor
            · intro h_mod_one
              exact List.sorted_mergeSort lst
            · intro h_mod_zero
              have : (lst.head! + lst.getLast?.getD 0) % 2 = 1 := h_odd
              simp [this] at h_mod_zero
      · simp [h_odd]
        constructor
        · simp [List.length_reverse, List.length_mergeSort]
        · constructor
          · intro i h_i
            constructor
            · simp [List.mem_reverse, List.mem_mergeSort]
              by_cases h_bound : i < lst.length
              · exact getElem_option_mem lst i h_bound
              · simp [List.getElem?_eq_none_iff] at h_bound
                simp [h_bound]
                exact List.mem_nil_iff.mp (False.elim (h_bound (by simp [List.length_reverse, List.length_mergeSort] at h_i; exact h_i)))
            · constructor
              · simp [List.mem_reverse, List.mem_mergeSort]
                by_cases h_bound : i < lst.length
                · exact getElem_option_mem lst i h_bound
                · simp [List.getElem?_eq_none_iff] at h_bound
                  simp [h_bound]
                  exact List.mem_nil_iff.mp (False.elim (h_bound (by simp [List.length_reverse, List.length_mergeSort] at h_i; exact h_i)))
              · simp [List.count_reverse, List.count_mergeSort]
          · constructor
            · intro h_mod_one
              simp [h_mod_one] at h_odd
            · intro h_mod_zero
              apply List.sorted_reverse_iff.mpr
              exact List.sorted_mergeSort lst