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
lemma foldl_max_int_ge_init (lst: List Int) (x: Int) :
  lst.foldl max_int x ≥ x := by
  induction lst generalizing x with
  | nil => simp
  | cons head tail ih =>
    simp
    apply le_trans (max_int_ge_left _ _)
    exact ih

-- LLM HELPER
lemma candidates_in_original (lst: List Int) :
  ∀ x ∈ lst.filter (fun x => lst.any (fun y => y < x)), x ∈ lst := by
  intro x hx
  exact List.mem_of_mem_filter hx

-- LLM HELPER
lemma nat_pos_of_ne_zero (n : Nat) : n ≠ 0 → 0 < n := by
  intro h
  exact Nat.pos_of_ne_zero h

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
        -- Show there exist i,j such that lst.get! i < lst.get! j
        have candidates_mem : x ∈ lst := by
          rw [hx] at h
          have x_in_candidates : x ∈ candidates := by
            rw [hx]
            simp
          exact candidates_in_original lst x x_in_candidates
        have x_in_candidates : x ∈ candidates := by
          rw [hx]
          simp
        have x_has_smaller : lst.any (fun y => y < x) := by
          simp [List.mem_filter] at x_in_candidates
          exact x_in_candidates.2
        obtain ⟨y, hy_mem, hy_lt⟩ := List.exists_mem_of_any_eq_true x_has_smaller
        have max_ge_x : max_candidate ≥ x := by
          rw [hx]
          exact foldl_max_int_ge_init xs x
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hy_mem
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp candidates_mem
        use i, j
        constructor
        · exact hi.1
        constructor
        · exact hj.1
        constructor
        · intro heq
          rw [heq] at hi
          rw [hj.2] at hi
          have : y < x := by
            rw [←hi.2]
            exact hy_lt
          linarith
        · rw [hi.2, hj.2]
          have : y < max_candidate := by
            linarith
          linarith
      · simp [h_len]
        by_cases h_all : (lst.filter (· < max_candidate)).all (λ y => y = (lst.filter (· < max_candidate)).get! 0)
        · simp [h_all]
          constructor
          · exact nat_pos_of_ne_zero _ h_len
          · exact h_all
        · simp [h_all]
          push_neg
          -- Show there exist i,j with lst.get! i < lst.get! j
          have candidates_mem : x ∈ lst := by
            rw [hx] at h
            have x_in_candidates : x ∈ candidates := by
              rw [hx]
              simp
            exact candidates_in_original lst x x_in_candidates
          have x_in_candidates : x ∈ candidates := by
            rw [hx]
            simp
          have x_has_smaller : lst.any (fun y => y < x) := by
            simp [List.mem_filter] at x_in_candidates
            exact x_in_candidates.2
          obtain ⟨y, hy_mem, hy_lt⟩ := List.exists_mem_of_any_eq_true x_has_smaller
          have max_ge_x : max_candidate ≥ x := by
            rw [hx]
            exact foldl_max_int_ge_init xs x
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp hy_mem
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp candidates_mem
          use i, j
          constructor
          · exact hi.1
          constructor
          · exact hj.1
          constructor
          · intro heq
            rw [heq] at hi
            rw [hj.2] at hi
            have : y < x := by
              rw [←hi.2]
              exact hy_lt
            linarith
          · rw [hi.2, hj.2]
            have : y < max_candidate := by
              linarith
            linarith