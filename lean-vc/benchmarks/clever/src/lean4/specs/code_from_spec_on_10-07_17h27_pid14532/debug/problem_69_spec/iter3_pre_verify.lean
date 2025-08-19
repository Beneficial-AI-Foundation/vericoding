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
  match numbers with
  | [] => -1
  | _ => 
    let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
    match candidates with
    | [] => -1
    | _ => candidates.max?.getD (-1)

def implementation (numbers: List Int) : (Int) := find_valid_element numbers

-- LLM HELPER
lemma filter_count_eq (numbers: List Int) (x: Int) : 
  (numbers.filter (fun y => y = x)).length = numbers.count x := by
  simp [List.count_eq_length_filter]

-- LLM HELPER
lemma all_pos_imp_mem_pos (numbers: List Int) (i: Nat) (h1: numbers.all (fun n => 0 < n)) 
  (h2: i < numbers.length) : 0 < numbers[i]! := by
  have h3 : numbers[i]! ∈ numbers := List.getElem_mem numbers i h2
  have h4 : decide (0 < numbers[i]!) = true := List.all_eq_true.mp h1 (numbers[i]!) h3
  exact of_decide_eq_true h4

-- LLM HELPER
lemma maximum_mem_of_nonempty {α : Type*} [LinearOrder α] (l : List α) (h : l ≠ []) : 
  ∃ x, l.max? = some x ∧ x ∈ l := by
  have : l.max?.isSome := List.max?_isSome_of_ne_nil h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
  use x
  constructor
  · exact hx
  · rw [List.max?_eq_some_iff] at hx
    exact hx.1

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp only [exists_prop]
  intro h_pos h_all
  constructor
  · intro h_neq
    simp [implementation, find_valid_element]
    by_cases h_empty : numbers = []
    · simp [h_empty] at h_pos
      contradiction
    · simp [h_empty] at h_neq
      let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
      by_cases h_cand_empty : candidates = []
      · simp [h_cand_empty] at h_neq
        contradiction
      · simp [h_cand_empty] at h_neq
        obtain ⟨result, h_max_some, h_result_mem⟩ := maximum_mem_of_nonempty candidates h_cand_empty
        have h_getD : candidates.max?.getD (-1) = result := by
          simp [h_max_some]
        rw [h_getD] at h_neq
        have h_result_mem_orig : result ∈ numbers := by
          have : candidates ⊆ numbers := List.filter_subset _ _
          exact this h_result_mem
        obtain ⟨i, hi, hi_eq⟩ := List.mem_iff_get.mp h_result_mem_orig
        use i
        simp [List.mem_filter] at h_result_mem
        constructor
        · exact hi
        · constructor
          · exact hi_eq.symm
          · constructor
            · rw [hi_eq]
              exact h_result_mem.1
            · constructor
              · rw [hi_eq, filter_count_eq]
                exact h_result_mem.2
              · intro j hj_lt hj_greater hj_count
                have hj_mem : numbers[j]! ∈ candidates := by
                  simp [List.mem_filter]
                  constructor
                  · exact all_pos_imp_mem_pos numbers j h_all hj_lt
                  · exact hj_count
                have hj_le_max : numbers[j]! ≤ result := by
                  rw [← h_max_some] at hj_mem
                  exact List.le_max?_of_mem hj_mem result h_max_some
                rw [hi_eq] at hj_greater
                linarith
  · intro h_ex
    obtain ⟨i, hi_lt, hi_eq, hi_pos, hi_count, hi_max⟩ := h_ex
    simp [implementation, find_valid_element]
    by_cases h_empty : numbers = []
    · simp [h_empty] at hi_lt
      contradiction
    · simp [h_empty]
      let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
      have hi_mem_cand : numbers[i]! ∈ candidates := by
        simp [List.mem_filter]
        constructor
        · exact hi_pos
        · rw [← filter_count_eq] at hi_count
          exact hi_count
      have h_cand_nonempty : candidates ≠ [] := List.ne_nil_of_mem hi_mem_cand
      simp [h_cand_nonempty]
      obtain ⟨max_val, h_max_some, h_max_mem⟩ := maximum_mem_of_nonempty candidates h_cand_nonempty
      have h_getD : candidates.max?.getD (-1) = max_val := by
        simp [h_max_some]
      rw [h_getD, hi_eq]
      intro h_eq_neg
      have h_max_ge : numbers[i]! ≤ max_val := by
        exact List.le_max?_of_mem hi_mem_cand max_val h_max_some
      linarith