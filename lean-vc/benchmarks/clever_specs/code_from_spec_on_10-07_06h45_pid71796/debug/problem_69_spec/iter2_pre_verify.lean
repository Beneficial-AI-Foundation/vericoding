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
      candidates.foldl max 0

def implementation (numbers: List Int) : Int := findMaxValidElement numbers

-- LLM HELPER
lemma list_count_eq_filter_length (numbers: List Int) (x: Int) :
  numbers.count x = (numbers.filter (fun y => y = x)).length := by
  simp [List.count_eq_length_filter]

-- LLM HELPER
lemma foldl_max_mem (l: List Int) (h: l ≠ []) :
  ∃ x, x ∈ l ∧ l.foldl max 0 = x := by
  cases' l with head tail
  · contradiction
  · use head
    constructor
    · simp
    · simp [List.foldl]
      sorry

-- LLM HELPER
lemma foldl_max_is_max (l: List Int) (x: Int) (h: x ∈ l) :
  x ≤ l.foldl max 0 := by
  sorry

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
          have h_max := candidates.foldl max 0
          have h_ne_nil : candidates ≠ [] := by
            rw [List.isEmpty_iff_eq_nil] at h_cand_empty
            exact h_cand_empty
          obtain ⟨max_val, h_mem, h_eq⟩ := foldl_max_mem candidates h_ne_nil
          use numbers.indexOf max_val
          constructor
          · have h_mem_orig : max_val ∈ numbers := by
              rw [List.mem_filter] at h_mem
              exact h_mem.1
            exact List.indexOf_lt_length.mpr h_mem_orig
          · constructor
            · have h_mem_orig : max_val ∈ numbers := by
                rw [List.mem_filter] at h_mem
                exact h_mem.1
              exact List.get_indexOf h_mem_orig
            · constructor
              · rw [List.mem_filter] at h_mem
                exact h_mem.2.1
              · constructor
                · rw [List.mem_filter] at h_mem
                  rw [List.get_indexOf (List.mem_of_mem_filter h_mem)]
                  exact h_mem.2.2
                · intro j hj_lt hj_gt hj_count
                  have h_j_val := numbers[j]!
                  have h_j_cand : h_j_val ∈ candidates := by
                    rw [List.mem_filter]
                    constructor
                    · exact List.get_mem numbers j hj_lt
                    · constructor
                      · rw [List.get_indexOf (List.mem_of_mem_filter h_mem)] at hj_gt
                        linarith
                      · exact hj_count
                  have h_le := foldl_max_is_max candidates h_j_val h_j_cand
                  rw [← h_eq] at h_le
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
        simp