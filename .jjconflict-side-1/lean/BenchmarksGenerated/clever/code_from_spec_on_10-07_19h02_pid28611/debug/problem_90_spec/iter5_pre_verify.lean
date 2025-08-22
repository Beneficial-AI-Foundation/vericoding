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
lemma no_pairs_when_empty (lst: List Int) : 
  lst = [] → ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j) := by
  intro h
  simp [h]
  intro i j hi
  simp [List.length_nil] at hi
  exact Nat.not_lt_zero i hi

-- LLM HELPER
lemma no_pairs_when_singleton (lst: List Int) (x: Int) :
  lst = [x] → ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst.get! i < lst.get! j) := by
  intro h
  simp [h]
  intro i j hi hj hne
  simp [List.length_singleton] at hi hj
  interval_cases i <;> interval_cases j <;> simp at hne

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
lemma candidates_mem_original (lst: List Int) (x: Int) :
  x ∈ lst.filter (fun y => lst.any (fun z => z < y)) → x ∈ lst := by
  intro h
  simp [List.mem_filter] at h
  exact h.1

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
      by_cases h_cond : lst.filter (· < max_candidate) = [] ∨ ¬(lst.filter (· < max_candidate)).all (λ y => y = (lst.filter (· < max_candidate)).get! 0)
      · simp [h_cond]
        cases' h_cond with h1 h2
        · simp [List.filter_eq_nil_iff] at h1
          push_neg at h1
          intro i j hi hj hne hlt
          have hi_mem : lst.get! i ∈ lst := by
            apply List.get!_mem
            simp [List.length_pos_iff_ne_nil]
            intro hlst_empty
            rw [hlst_empty] at hi
            simp at hi
          specialize h1 (lst.get! i) hi_mem
          have : max_candidate ≥ lst.get! j := by
            have hj_mem : lst.get! j ∈ lst := by
              apply List.get!_mem
              simp [List.length_pos_iff_ne_nil]
              intro hlst_empty
              rw [hlst_empty] at hj
              simp at hj
            have hj_cand : lst.get! j ∈ candidates := by
              simp [List.mem_filter]
              constructor
              · exact hj_mem
              · simp [List.any_eq_true]
                use lst.get! i
                constructor
                · exact hi_mem
                · exact hlt
            have : lst.get! j ∈ (x :: xs) := by
              rw [← hx]
              exact hj_cand
            simp at this
            cases' this with h_eq h_mem
            · rw [h_eq]
              exact max_int_ge_left _ _
            · exact foldl_max_int_ge_mem xs (max_int x _) (lst.get! j) h_mem
          linarith
        · simp [List.all_eq_true] at h2
          push_neg at h2
          obtain ⟨y, hy_mem, hy_ne⟩ := h2
          simp [List.mem_filter] at hy_mem
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
          have hj_cand : lst.get! j ∈ candidates := by
            simp [List.mem_filter]
            constructor
            · exact hj_mem
            · simp [List.any_eq_true]
              use lst.get! i
              constructor
              · exact hi_mem
              · exact hlt
          have : lst.get! j ∈ (x :: xs) := by
            rw [← hx]
            exact hj_cand
          simp at this
          cases' this with h_eq h_mem
          · rw [h_eq]
            have : lst.get! i < max_candidate := by
              have : lst.get! i < x := by
                rw [← h_eq]
                exact hlt
              have : x ≤ max_candidate := max_int_ge_left _ _
              linarith
            have : lst.get! i ∈ lst.filter (· < max_candidate) := by
              simp [List.mem_filter]
              constructor
              · exact hi_mem
              · exact this
            have : lst.get! i = y := by
              by_contra hne_y
              have : lst.get! i ∈ lst.filter (· < max_candidate) := by
                simp [List.mem_filter]
                constructor
                · exact hi_mem
                · exact this
              have : lst.get! i = (lst.filter (· < max_candidate)).get! 0 := by
                simp [List.get!_zero_of_mem this]
              have : y = (lst.filter (· < max_candidate)).get! 0 := by
                simp [List.get!_zero_of_mem] at hy_mem
                exact hy_mem.2
              rw [this] at hy_ne
              exact hy_ne this
            rw [← this] at hy_ne
            exact hy_ne rfl
          · have : lst.get! i < max_candidate := by
              have : lst.get! i < lst.get! j := hlt
              have : lst.get! j ≤ max_candidate := by
                exact foldl_max_int_ge_mem xs (max_int x _) (lst.get! j) h_mem
              linarith
            have : lst.get! i ∈ lst.filter (· < max_candidate) := by
              simp [List.mem_filter]
              constructor
              · exact hi_mem
              · exact this
            have : lst.get! i = y := by
              by_contra hne_y
              have : lst.get! i = (lst.filter (· < max_candidate)).get! 0 := by
                simp [List.get!_zero_of_mem this]
              have : y = (lst.filter (· < max_candidate)).get! 0 := by
                simp [List.get!_zero_of_mem] at hy_mem
                exact hy_mem.2
              rw [this] at hy_ne
              exact hy_ne this
            rw [← this] at hy_ne
            exact hy_ne rfl
      · simp [h_cond]
        push_neg at h_cond
        constructor
        · simp [List.length_pos_iff_ne_nil]
          exact h_cond.1
        · exact h_cond.2