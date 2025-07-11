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
  exact List.mem_of_max?_eq_some h

-- LLM HELPER
lemma max_is_max {α : Type*} [LinearOrder α] (l : List α) (x : α) :
  l.max? = some x → ∀ y ∈ l, y ≤ x := by
  intro h y hy
  exact List.le_max_of_mem hy (Option.some.inj h)

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
      have hc : ∃ x ∈ numbers, 0 < x ∧ x ≤ numbers.count x := by
        by_contra hnc
        simp at hnc
        have h_empty : numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          simp
          exact hnc x hx
        simp [h_empty] at hne
        have all_pos : ∀ x ∈ numbers, 0 < x := by
          intro x hx
          have := List.all_eq_true.mp h.2 x hx
          exact of_decide_eq_true this
        obtain ⟨x, hx_mem⟩ := List.ne_nil_of_length_pos h.1
        have hx_pos := all_pos x hx_mem
        have hx_count : x ≤ numbers.count x := by
          have : numbers.count x ≥ 1 := by
            rw [List.count_pos]
            exact hx_mem
          linarith [hx_pos]
        have := hnc x hx_mem hx_pos hx_count
        contradiction
      have hne_nil : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) ≠ [] := by
        intro heq
        obtain ⟨x, hx_mem, hx_pos, hx_count⟩ := hc
        have hx_in_filter : x ∈ numbers.filter (fun y => y > 0 ∧ y ≤ numbers.count y) := by
          rw [List.mem_filter]
          exact ⟨hx_mem, hx_pos, hx_count⟩
        rw [heq] at hx_in_filter
        exact List.not_mem_nil x hx_in_filter
      cases' hmax_eq : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).max? with
      | none => 
        rw [List.max?_eq_none_iff] at hmax_eq
        contradiction
      | some max_val =>
        simp [hmax_eq] at hne
        have hmax_in := max_in_list (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) max_val hmax_eq
        have hmax_prop := List.mem_filter.mp hmax_in
        obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp hmax_prop.1
        use i, hi_lt
        constructor
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
                  · have hpos := List.all_eq_true.mp h.2 numbers[j]! (List.get_mem numbers j hj_lt)
                    exact of_decide_eq_true hpos
                  · exact hj_count
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
      cases' hmax_case : (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)).max? with
      | none => 
        rw [List.max?_eq_none_iff] at hmax_case
        contradiction
      | some max_val =>
        simp [hmax_case] at h_eq
        have hmax_ge := max_is_max (numbers.filter (fun x => x > 0 ∧ x ≤ numbers.count x)) max_val hmax_case numbers[i]! hi_in_filter
        rw [hi_eq] at hmax_ge
        rw [←hi_eq] at h_eq
        linarith