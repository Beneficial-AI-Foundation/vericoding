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
        | some max => aux xs (some (max.max x))
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
  sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  use find_max_with_smaller lst
  constructor
  · rfl
  · exact find_max_with_smaller_spec lst