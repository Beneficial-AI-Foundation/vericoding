import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Option Int) :=
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els.get! 0);
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def find_max_with_smaller (lst: List Int) : Option Int :=
  let rec aux (remaining: List Int) (current_max: Option Int) : Option Int :=
    match remaining with
    | [] => current_max
    | x :: xs =>
      let has_smaller := lst.any (· < x)
      if has_smaller then
        match current_max with
        | none => aux xs (some x)
        | some max => aux xs (some (Int.max max x))
      else
        aux xs current_max
  aux lst none

def implementation (lst: List Int) : Option Int := find_max_with_smaller lst

-- LLM HELPER
lemma filter_empty_iff_no_smaller (lst: List Int) (x: Int) :
  lst.filter (· < x) = [] ↔ ¬ lst.any (· < x) := by
  simp [List.filter_eq_nil_iff, List.any_eq_true]
  tauto

-- LLM HELPER
lemma find_max_with_smaller_spec (lst: List Int) :
  let result := find_max_with_smaller lst
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els.get! 0) := by
  unfold find_max_with_smaller
  simp
  by_cases h : lst = []
  · simp [h]
    intro i j hi hj
    simp [List.length_nil] at hi
    exact Nat.not_lt_zero i hi
  · simp [h]
    split
    · intro i j hi hj hne hlt
      simp at hi hj
      cases' Nat.not_lt_zero i hi
    · simp
      constructor
      · simp [List.length_pos_iff_ne_nil]
        apply List.ne_nil_of_mem
        simp [List.mem_filter]
        exists 0
        constructor
        · simp
        · simp
      · intro x hx
        simp [List.mem_filter] at hx
        simp [List.get!, List.get_eq_getElem]
        simp [List.filter_eq_cons_iff]
        tauto

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  use find_max_with_smaller lst
  constructor
  · rfl
  · exact find_max_with_smaller_spec lst