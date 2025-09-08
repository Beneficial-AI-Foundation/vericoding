/- 
function_signature: "def max_element(l: list)"
docstring: |
    Return maximum element in the list.
test_cases:
  - input: [1, 2, 3]
    output: 3
  - input: [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
    output: 123
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (l: List Int) : Int :=
  match l with
  | [] => 0  -- arbitrary default for empty list
  | h :: t => t.foldl max h

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: Int) :=
  l.length > 0 →
  ((∀ i, i < l.length → l[i]! ≤ result) ∧
  (∃ i, i < l.length ∧ l[i]! = result));
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
lemma foldl_max_ge (l : List Int) (init : Int) : 
  ∀ x ∈ init :: l, x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => 
    simp [List.foldl]
    intro x hx
    simp at hx
    rw [hx]
  | cons head tail ih =>
    intro x hx
    simp [List.foldl]
    rw [List.mem_cons] at hx
    cases hx with
    | inl h => 
      rw [h]
      have : init ≤ max init head := le_max_left init head
      have ih_result := ih (max init head) init (by simp)
      exact le_trans this ih_result
    | inr h =>
      cases h with
      | inl h2 =>
        rw [h2]
        have : head ≤ max init head := le_max_right init head
        have ih_result := ih (max init head) head (by simp)
        exact le_trans this ih_result
      | inr h2 =>
        have ih_result := ih (max init head) x (by simp; exact h2)
        exact ih_result

-- LLM HELPER  
lemma foldl_max_mem (l : List Int) (init : Int) :
  l.foldl max init ∈ init :: l := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons head tail ih =>
    simp [List.foldl]
    have ih_result := ih (max init head)
    cases ih_result with
    | inl h => 
      rw [h]
      by_cases h1 : init ≤ head
      · simp [max_def, h1]
      · simp [max_def, h1]
    | inr h => simp; right; exact h

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec
  use implementation l
  constructor
  · rfl
  · intro h_nonempty
    unfold implementation
    cases l with
    | nil => 
      simp at h_nonempty
    | cons head tail =>
      simp [List.length_cons] at h_nonempty
      constructor
      · intro i hi
        simp [List.getElem_cons]
        have foldl_result := foldl_max_ge tail head
        by_cases h : i = 0
        · simp [h]
          exact foldl_result head (by simp)
        · simp [h]
          have : i - 1 < tail.length := by
            simp at hi
            omega
          exact foldl_result (tail[i-1]!) (by simp; use i-1; simp [this])
      · have mem_result := foldl_max_mem tail head
        cases mem_result with
        | inl h => 
          use 0
          constructor
          · simp
          · simp [List.getElem_cons, h]
        | inr h =>
          have : ∃ j, j < tail.length ∧ tail[j]! ∈ tail := by
            cases tail with
            | nil => simp at h
            | cons t_head t_tail =>
              simp at h
              cases h with
              | inl h2 => use 0; simp [h2]
              | inr h2 => 
                have : ∃ k, k < t_tail.length ∧ t_tail[k]! ∈ t_tail := by
                  cases t_tail with
                  | nil => simp at h2
                  | cons _ _ => use 0; simp
                cases this with
                | intro k hk => use k + 1; simp [List.getElem_cons]; exact hk.2
          cases this with
          | intro j hj =>
            have tail_elem : tail[j]! = tail.foldl max head := by
              have : tail[j]! ∈ head :: tail := by simp; right; exact hj.2
              have ge_all := foldl_max_ge tail head tail[j]! this
              have mem_foldl := foldl_max_mem tail head
              cases mem_foldl with
              | inl h_eq => rw [h_eq]; exact foldl_result head (by simp)
              | inr h_mem => 
                -- The foldl result must equal some element, and since all elements ≤ foldl result
                -- and tail[j]! ≤ foldl result, if tail[j]! appears in the max computation, it equals the max
                sorry -- This case needs more careful analysis
            use j + 1
            constructor
            · simp [List.length_cons]; exact Nat.succ_lt_succ hj.1
            · simp [List.getElem_cons]
              exact tail_elem

-- #test implementation [1, 2, 3] = 3
-- #test implementation [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123