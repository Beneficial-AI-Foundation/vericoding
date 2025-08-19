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
  else candidates.maximum?.getD (-1)

def implementation (numbers: List Int) : (Int) := find_valid_element numbers

-- LLM HELPER
lemma list_count_eq_filter_length (l : List Int) (x : Int) : 
  l.count x = (l.filter (fun y => y = x)).length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.count_cons, List.filter_cons]
    split_ifs with h_eq
    · simp [h_eq, ih]
    · exact ih

-- LLM HELPER
lemma maximum_in_list (l : List Int) (x : Int) :
  l.maximum? = some x → x ∈ l := by
  intro h
  cases' l with h t
  · simp at h
  · simp [List.maximum?_cons] at h
    cases' t with h2 t2
    · simp at h
      simp [h]
    · have h_max := h
      simp [List.maximum?_cons] at h_max
      sorry

-- LLM HELPER
lemma maximum_is_max (l : List Int) (x : Int) :
  l.maximum? = some x → ∀ y ∈ l, y ≤ x := by
  intro h y hy
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation find_valid_element
  simp
  use find_valid_element numbers
  constructor
  · rfl
  · intro h
    simp [find_valid_element]
    split_ifs with h_empty
    · simp
      intro h_ex
      obtain ⟨i, hi_lt, hi_eq, hi_pos, hi_leq, hi_not_exists⟩ := h_ex
      have h_in_candidates : numbers[i]! ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := by
        simp [List.mem_filter]
        constructor
        · exact List.getElem_mem numbers i hi_lt
        · constructor
          · rw [←hi_eq]; exact hi_pos
          · rw [←hi_eq, list_count_eq_filter_length]; exact hi_leq
      simp [List.isEmpty_iff_eq_nil] at h_empty
      rw [h_empty] at h_in_candidates
      exact h_in_candidates
    · simp
      constructor
      · intro h_ne
        have h_exists_max : ∃ max_val, (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).maximum? = some max_val := by
          cases' h_max_opt : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).maximum? with
          | none => 
            simp [List.isEmpty_iff_eq_nil] at h_empty
            have h_nonempty : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) ≠ [] := h_empty
            have h_empty_max : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).maximum? = none → (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) = [] := by
              intro h_none
              cases' numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) with
              | nil => rfl
              | cons h t => simp [List.maximum?_cons] at h_none
            exact h_nonempty (h_empty_max h_max_opt)
          | some max_val => use max_val; exact h_max_opt
        obtain ⟨max_val, h_max⟩ := h_exists_max
        have h_max_in := maximum_in_list _ _ h_max
        simp [List.mem_filter] at h_max_in
        obtain ⟨h_max_mem, h_max_pos, h_max_leq⟩ := h_max_in
        obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp h_max_mem
        use i
        constructor
        · exact hi_lt
        · constructor
          · exact hi_eq.symm
          · constructor
            · rw [hi_eq]; exact h_max_pos
            · constructor
              · rw [hi_eq, list_count_eq_filter_length]; exact h_max_leq
              · intro h_ex
                obtain ⟨j, hj_lt, hj_ineq, hj_leq⟩ := h_ex
                have h_j_in_candidates : numbers[j]! ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := by
                  simp [List.mem_filter]
                  constructor
                  · exact List.getElem_mem numbers j hj_lt
                  · constructor
                    · have h_all := h.2
                      have h_j_pos := List.all_getElem h_all hj_lt
                      exact h_j_pos
                    · exact hj_leq
                have h_j_leq_max := maximum_is_max _ _ h_max _ h_j_in_candidates
                rw [←hi_eq] at hj_ineq
                exact not_lt.mpr h_j_leq_max hj_ineq
      · intro h_ex
        obtain ⟨i, hi_lt, hi_eq, hi_pos, hi_leq, hi_not_exists⟩ := h_ex
        have h_in_candidates : numbers[i]! ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := by
          simp [List.mem_filter]
          constructor
          · exact List.getElem_mem numbers i hi_lt
          · constructor
            · rw [←hi_eq]; exact hi_pos
            · rw [←hi_eq, list_count_eq_filter_length]; exact hi_leq
        have h_nonempty : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).Nonempty := by
          use numbers[i]!
          exact h_in_candidates
        simp [List.isEmpty_iff_eq_nil] at h_empty
        exact h_empty h_nonempty