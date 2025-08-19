def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: Int) :=
0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
(result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
  numbers[i]! = result ∧ numbers[i]! > 0 ∧
  numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
  (¬∃ j : Nat, j < numbers.length ∧
  numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def findMaxValidElement (numbers: List Int) : Int :=
  if numbers.isEmpty then
    -1
  else
    let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
    if candidates.isEmpty then
      -1
    else
      candidates.maximum?.getD (-1)

def implementation (numbers: List Int) : (Int) := findMaxValidElement numbers

-- LLM HELPER
lemma list_count_eq_filter_length (numbers: List Int) (x: Int) :
  numbers.count x = (numbers.filter (fun y => y = x)).length := by
  simp [List.count_eq_length_filter]

-- LLM HELPER
lemma maximum_exists_in_nonempty (l: List Int) (h: l ≠ []) :
  ∃ x, x ∈ l ∧ l.maximum? = some x := by
  cases' l with head tail
  · contradiction
  · simp [List.maximum?]
    exact List.maximum_mem (head :: tail)

-- LLM HELPER
lemma maximum_is_max (l: List Int) (x: Int) (h: l.maximum? = some x) :
  x ∈ l ∧ ∀ y ∈ l, y ≤ x := by
  constructor
  · exact List.maximum?_mem h
  · intro y hy
    exact List.le_maximum_of_mem hy (List.maximum?_mem h)

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation findMaxValidElement
  simp only [exists_prop]
  constructor
  · rfl
  · intro h
    simp [List.count_eq_length_filter] at *
    constructor
    · intro hneq
      by_cases h_empty : numbers.isEmpty
      · simp [h_empty] at hneq
        contradiction
      · simp [h_empty] at hneq
        let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
        by_cases h_cand_empty : candidates.isEmpty
        · simp [h_cand_empty] at hneq
          contradiction
        · simp [h_cand_empty] at hneq
          have h_max := candidates.maximum?.getD (-1)
          have h_some : candidates.maximum? ≠ none := by
            rw [List.maximum?_eq_none_iff]
            exact h_cand_empty
          obtain ⟨max_val, h_max_eq⟩ := Option.ne_none_iff_exists'.mp h_some
          rw [Option.getD_some h_max_eq] at hneq
          use numbers.indexOf max_val
          constructor
          · have h_mem : max_val ∈ candidates := List.maximum?_mem h_max_eq
            have h_mem_orig : max_val ∈ numbers := by
              rw [List.mem_filter] at h_mem
              exact h_mem.1
            exact List.indexOf_lt_length.mpr h_mem_orig
          · constructor
            · have h_mem : max_val ∈ candidates := List.maximum?_mem h_max_eq
              have h_mem_orig : max_val ∈ numbers := by
                rw [List.mem_filter] at h_mem
                exact h_mem.1
              exact List.get_indexOf h_mem_orig
            · constructor
              · have h_mem : max_val ∈ candidates := List.maximum?_mem h_max_eq
                rw [List.mem_filter] at h_mem
                exact h_mem.2.1
              · constructor
                · have h_mem : max_val ∈ candidates := List.maximum?_mem h_max_eq
                  rw [List.mem_filter] at h_mem
                  rw [List.get_indexOf (List.mem_of_mem_filter h_mem)]
                  exact h_mem.2.2
                · intro j hj_lt hj_gt hj_count
                  have h_mem : max_val ∈ candidates := List.maximum?_mem h_max_eq
                  have h_j_val := numbers[j]!
                  have h_j_cand : h_j_val ∈ candidates := by
                    rw [List.mem_filter]
                    constructor
                    · exact List.get_mem numbers j hj_lt
                    · constructor
                      · rw [List.get_indexOf (List.mem_of_mem_filter h_mem)] at hj_gt
                        linarith
                      · exact hj_count
                  have h_max_prop := (maximum_is_max candidates max_val h_max_eq).2
                  have h_le := h_max_prop h_j_val h_j_cand
                  rw [List.get_indexOf (List.mem_of_mem_filter h_mem)] at hj_gt
                  linarith
    · intro h_exists
      obtain ⟨i, hi_lt, hi_eq, hi_pos, hi_count, hi_max⟩ := h_exists
      by_cases h_empty : numbers.isEmpty
      · simp [List.length_eq_zero] at h_empty
        rw [h_empty] at hi_lt
        simp at hi_lt
      · simp [h_empty]
        let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
        have h_i_in_cand : numbers[i]! ∈ candidates := by
          rw [List.mem_filter]
          constructor
          · exact List.get_mem numbers i hi_lt
          · constructor
            · rw [← hi_eq]
              exact hi_pos
            · rw [← hi_eq]
              exact hi_count
        have h_cand_nonempty : ¬candidates.isEmpty := by
          intro h_contra
          rw [List.isEmpty_iff_eq_nil] at h_contra
          rw [h_contra] at h_i_in_cand
          exact h_i_in_cand
        simp [h_cand_nonempty]
        have h_max := candidates.maximum?.getD (-1)
        have h_some : candidates.maximum? ≠ none := by
          rw [List.maximum?_eq_none_iff]
          exact h_cand_nonempty
        obtain ⟨max_val, h_max_eq⟩ := Option.ne_none_iff_exists'.mp h_some
        rw [Option.getD_some h_max_eq]
        have h_max_prop := (maximum_is_max candidates max_val h_max_eq).2
        have h_le := h_max_prop (numbers[i]!) h_i_in_cand
        have h_i_max : ∀ j, j < numbers.length → numbers[i]! < numbers[j]! → ¬(numbers[j]! ≤ numbers.count numbers[j]!) := hi_max
        by_contra h_eq
        rw [h_eq] at h_le
        rw [← hi_eq] at h_le
        have h_max_mem := List.maximum?_mem h_max_eq
        have h_max_in_orig : max_val ∈ numbers := by
          rw [List.mem_filter] at h_max_mem
          exact h_max_mem.1
        obtain ⟨j, hj_lt, hj_eq⟩ := List.mem_iff_get.mp h_max_in_orig
        rw [← hj_eq] at h_le
        rw [← hi_eq] at h_le
        by_cases h_case : numbers[i]! < numbers[j]!
        · have h_j_not_count := h_i_max j hj_lt h_case
          rw [hj_eq] at h_max_mem
          rw [List.mem_filter] at h_max_mem
          exact h_j_not_count h_max_mem.2.2
        · push_neg at h_case
          have h_eq_case : numbers[i]! = numbers[j]! := by
            exact Nat.eq_of_le_of_lt_succ h_case (Nat.lt_succ_of_le h_le)
          rw [hi_eq, hj_eq, h_eq_case]