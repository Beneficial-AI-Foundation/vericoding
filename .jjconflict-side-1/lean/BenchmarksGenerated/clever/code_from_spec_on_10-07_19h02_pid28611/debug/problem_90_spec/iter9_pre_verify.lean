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
def max_int (x y : Int) : Int := if x ≥ y then x else y

def implementation (lst: List Int) : Option Int :=
  let candidates := lst.filter (fun x => lst.any (fun y => y < x))
  match candidates with
  | [] => none
  | x :: _ => 
    let max_candidate := candidates.foldl max_int x
    let smaller_elements := lst.filter (· < max_candidate)
    if smaller_elements.length > 0 ∧ smaller_elements.all (λ y => y = smaller_elements.get! 0)
    then some max_candidate
    else none

-- LLM HELPER
lemma max_int_ge_left (x y : Int) : max_int x y ≥ x := by
  unfold max_int
  by_cases h : x ≥ y
  · simp [h]
  · simp [h]
    linarith

-- LLM HELPER
lemma max_int_ge_right (x y : Int) : max_int x y ≥ y := by
  unfold max_int
  by_cases h : x ≥ y
  · simp [h]
    exact h
  · simp [h]

-- LLM HELPER
lemma foldl_max_int_ge_mem (lst: List Int) (x: Int) (y: Int) :
  y ∈ lst → lst.foldl max_int x ≥ y := by
  intro h
  induction lst generalizing x with
  | nil => simp at h
  | cons head tail ih =>
    simp at h
    cases' h with h1 h2
    · simp [h1]
      exact max_int_ge_right _ _
    · simp
      apply ih
      exact h2

-- LLM HELPER
lemma no_candidates_no_pairs (lst: List Int) :
  lst.filter (fun x => lst.any (fun y => y < x)) = [] → 
  ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j) := by
  intro h
  simp [List.filter_eq_nil_iff] at h
  push_neg
  intro i j hi hj hne hlt
  have hi_mem : lst.get! i ∈ lst := by
    apply List.get!_mem
    simp [List.length_pos_iff_ne_nil]
    intro hlst_empty
    rw [hlst_empty] at hi
    simp at hi
  have hj_mem : lst.get! j ∈ lst := by
    apply List.get!_mem
    simp [List.length_pos_iff_ne_nil]
    intro hlst_empty
    rw [hlst_empty] at hj
    simp at hj
  specialize h (lst.get! j) hj_mem
  simp [List.any_eq_true] at h
  push_neg at h
  specialize h (lst.get! i) hi_mem
  linarith

-- LLM HELPER
lemma get_mem_of_lt_length (lst: List Int) (i: Nat) :
  i < lst.length → lst.get! i ∈ lst := by
  intro h
  apply List.get!_mem
  simp [List.length_pos_iff_ne_nil]
  intro hlst_empty
  rw [hlst_empty] at h
  simp at h

-- LLM HELPER
lemma foldl_max_int_ge_init (lst: List Int) (x: Int) :
  lst.foldl max_int x ≥ x := by
  induction lst generalizing x with
  | nil => simp
  | cons head tail ih =>
    simp
    apply le_trans (max_int_ge_left _ _)
    exact ih

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec implementation
  use implementation lst
  constructor
  · rfl
  · unfold implementation
    let candidates := lst.filter (fun x => lst.any (fun y => y < x))
    by_cases h : candidates = []
    · simp [h]
      exact no_candidates_no_pairs lst h
    · simp [h]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil h
      simp [hx]
      let max_candidate := candidates.foldl max_int x
      by_cases h_len : (lst.filter (· < max_candidate)).length = 0
      · simp [h_len]
        push_neg
        sorry
      · simp [h_len]
        by_cases h_all : (lst.filter (· < max_candidate)).all (λ y => y = (lst.filter (· < max_candidate)).get! 0)
        · simp [h_all]
          constructor
          · linarith
          · exact h_all
        · simp [h_all]
          push_neg
          sorry