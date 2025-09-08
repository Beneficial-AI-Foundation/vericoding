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
      have ih_result := ih (max init head) (max init head) (by simp)
      exact le_trans this ih_result
    | inr h =>
      rw [List.mem_cons] at h
      cases h with
      | inl h2 =>
        rw [h2]
        have : head ≤ max init head := le_max_right init head
        have ih_result := ih (max init head) (max init head) (by simp)
        exact le_trans this ih_result
      | inr h2 =>
        have ih_result := ih (max init head) x (by simp [Or.inr, h2])
        exact ih_result

-- LLM HELPER  
lemma foldl_max_mem (l : List Int) (init : Int) :
  l.foldl max init ∈ init :: l := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons head tail ih =>
    simp [List.foldl]
    have ih_result := ih (max init head)
    rw [List.mem_cons] at ih_result
    cases ih_result with
    | inl h => 
      rw [h]
      by_cases h1 : init ≤ head
      · simp [max_def, h1]; right; left; rfl
      · simp [max_def, h1]; left; rfl
    | inr h => simp [Or.inr, Or.inr, h]

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
        simp
        have foldl_result := foldl_max_ge tail head
        by_cases h : i = 0
        · simp [h]
          exact foldl_result head (by simp)
        · simp [h]
          have i_pos : 0 < i := Nat.pos_of_ne_zero h
          have i_le : i ≤ tail.length := by
            simp at hi
            omega
          have : i - 1 < tail.length := by
            simp at hi
            omega
          have tail_elem := List.get_mem tail ⟨i-1, this⟩
          have tail_mem : tail.get ⟨i-1, this⟩ ∈ head :: tail := by
            simp [Or.inr]
            exact tail_elem
          have get_eq : (head :: tail)[i]?.getD 0 = tail[i - 1] := by
            simp [List.getElem?_cons_succ]
            rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
          exact foldl_result (tail.get ⟨i-1, this⟩) tail_mem
      · have mem_result := foldl_max_mem tail head
        rw [List.mem_cons] at mem_result
        cases mem_result with
        | inl h => 
          use 0
          constructor
          · simp
          · simp [h]
        | inr h =>
          obtain ⟨j, hj_eq⟩ := List.mem_iff_get.mp h
          use j.val + 1
          constructor
          · simp [List.length_cons]
            exact Nat.succ_lt_succ j.isLt
          · simp [List.getElem_cons_succ]
            rw [← hj_eq]
            rfl