import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def find_valid_element (numbers: List Int) : Int :=
  let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
  if candidates.isEmpty then -1
  else
    let max_candidate := candidates.maximum?
    match max_candidate with
    | none => -1
    | some max_val => max_val

def implementation (numbers: List Int) : (Int) := find_valid_element numbers

-- LLM HELPER
lemma filter_count_le (numbers: List Int) (x: Int) : 
  (numbers.filter (fun y => y = x)).length = numbers.count x := by
  simp [List.count_eq_length_filter]

-- LLM HELPER
lemma exists_result : ∀ numbers : List Int, ∃ result : Int, implementation numbers = result := by
  intro numbers
  use implementation numbers
  rfl

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp only [implementation]
  use find_valid_element numbers
  constructor
  · rfl
  · intro h
    unfold find_valid_element
    simp only [ite_eq_right_iff]
    constructor
    · intro h_neq_neg_one
      by_cases h_empty : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).isEmpty
      · simp [h_empty] at h_neq_neg_one
      · simp [h_empty] at h_neq_neg_one ⊢
        have h_nonempty : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).length > 0 := by
          rw [List.length_pos_iff_ne_nil]
          rwa [← List.isEmpty_iff_eq_nil]
        obtain ⟨max_val, h_max⟩ := List.maximum?_eq_some_iff.mp ⟨h_nonempty, rfl⟩
        simp [h_max.1] at h_neq_neg_one ⊢
        have h_in_filtered : max_val ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := h_max.2.1
        have h_mem : max_val ∈ numbers := List.mem_of_mem_filter h_in_filtered
        obtain ⟨i, h_i_lt, h_i_eq⟩ := List.mem_iff_get.mp h_mem
        use i
        constructor
        · exact h_i_lt
        · constructor
          · rw [← h_i_eq]
            simp [List.get_eq_getElem]
          · have h_props : max_val > 0 ∧ max_val ≤ numbers.count max_val := 
              List.mem_filter.mp h_in_filtered |>.2
            constructor
            · exact h_props.1
            · constructor
              · rw [← filter_count_le]
                exact h_props.2
              · intro ⟨j, h_j_lt, h_less, h_count⟩
                have h_j_in_filtered : numbers[j]! ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := by
                  simp [List.mem_filter]
                  constructor
                  · exact List.getElem_mem numbers j h_j_lt
                  · constructor
                    · have : numbers[j]! > max_val := h_less
                      have : max_val > 0 := h_props.1
                      linarith
                    · exact h_count
                have h_max_ge := h_max.2.2 (numbers[j]!) h_j_in_filtered
                linarith [h_less]
    · intro h_exists
      obtain ⟨i, h_i_lt, h_i_eq, h_pos, h_count, h_max⟩ := h_exists
      by_cases h_empty : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).isEmpty
      · have h_in_filtered : numbers[i]! ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := by
          simp [List.mem_filter]
          constructor
          · exact List.getElem_mem numbers i h_i_lt
          · constructor
            · exact h_pos
            · rw [filter_count_le] at h_count
              exact h_count
        rw [List.isEmpty_iff_eq_nil] at h_empty
        rw [h_empty] at h_in_filtered
        exact List.not_mem_nil _ h_in_filtered
      · simp [h_empty]
        have h_nonempty : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).length > 0 := by
          rw [List.length_pos_iff_ne_nil]
          rwa [← List.isEmpty_iff_eq_nil]
        obtain ⟨max_val, h_max_some⟩ := List.maximum?_eq_some_iff.mp ⟨h_nonempty, rfl⟩
        simp [h_max_some.1]
        linarith [h_max_some.2.2]