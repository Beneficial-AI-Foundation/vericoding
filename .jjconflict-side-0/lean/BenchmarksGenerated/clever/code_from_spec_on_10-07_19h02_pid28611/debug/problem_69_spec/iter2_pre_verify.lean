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
def findValidNumber (numbers: List Int) : Int :=
  let candidates := numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)
  match candidates with
  | [] => -1
  | _ => candidates.max?.getD (-1)

def implementation (numbers: List Int) : (Int) := findValidNumber numbers

-- LLM HELPER
lemma count_eq_filter_length (numbers: List Int) (x: Int) :
  numbers.count x = (numbers.filter (fun y => y = x)).length := by
  rw [List.count_eq_length_filter]

-- LLM HELPER
lemma max_in_list {α : Type*} [LinearOrder α] (l : List α) (x : α) :
  l.max? = some x → x ∈ l := by
  intro h
  exact List.max?_mem h

-- LLM HELPER
lemma max_is_max {α : Type*} [LinearOrder α] (l : List α) (x : α) :
  l.max? = some x → ∀ y ∈ l, y ≤ x := by
  intro h y hy
  exact List.le_max?_of_mem hy h

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation findValidNumber
  use findValidNumber numbers
  constructor
  · rfl
  · intro h
    constructor
    · intro hne
      by_cases hc : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).isEmpty
      · simp [List.max?_eq_none_iff] at hc
        simp [hc] at hne
        contradiction
      · simp [List.isEmpty_iff] at hc
        cases' hmax_eq : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).max? with
        | none => 
          simp [List.max?_eq_none_iff] at hmax_eq
          contradiction
        | some max_val =>
          simp [hmax_eq] at hne
          have hmax_in := max_in_list (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) max_val hmax_eq
          have hmax_prop := List.mem_filter.mp hmax_in
          obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp hmax_prop.1
          use i
          constructor
          · exact hi_lt
          · constructor
            · exact hi_eq.symm
            · constructor
              · rw [hi_eq]
                exact hmax_prop.2.1
              · constructor
                · rw [hi_eq, count_eq_filter_length]
                  exact hmax_prop.2.2
                · intro ⟨j, hj_lt, hj_greater, hj_count⟩
                  have hj_in_filter : numbers[j]! ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := by
                    rw [List.mem_filter]
                    constructor
                    · exact List.get_mem numbers j hj_lt
                    · constructor
                      · have hpos := List.all_iff_forall.mp h.2 numbers[j]! (List.get_mem numbers j hj_lt)
                        exact hpos
                      · rw [count_eq_filter_length]
                        exact hj_count
                  have hmax_ge := max_is_max (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) max_val hmax_eq numbers[j]! hj_in_filter
                  rw [←hi_eq] at hmax_ge
                  linarith [hj_greater]
    · intro hex
      obtain ⟨i, hi_lt, hi_eq, hi_pos, hi_count, hi_max⟩ := hex
      by_contra h_eq
      have hi_in_filter : numbers[i]! ∈ numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) := by
        rw [List.mem_filter]
        constructor
        · exact List.get_mem numbers i hi_lt
        · constructor
          · exact hi_pos
          · rw [count_eq_filter_length]
            exact hi_count
      have hne_nil : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) ≠ [] := by
        intro heq
        rw [heq] at hi_in_filter
        exact List.not_mem_nil numbers[i]! hi_in_filter
      simp [List.max?_eq_none_iff] at h_eq
      simp [hne_nil] at h_eq
      cases' hmax_case : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).max? with
      | none => 
        simp [List.max?_eq_none_iff] at hmax_case
        contradiction
      | some max_val =>
        simp [hmax_case] at h_eq
        have hmax_ge := max_is_max (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) max_val hmax_case numbers[i]! hi_in_filter
        rw [hi_eq] at hmax_ge
        rw [←hi_eq] at h_eq
        linarith