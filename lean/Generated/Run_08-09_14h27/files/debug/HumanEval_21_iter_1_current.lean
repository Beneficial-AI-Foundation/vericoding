import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def list_min (l : List Rat) : Rat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => min x (list_min xs)

-- LLM HELPER
def list_max (l : List Rat) : Rat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => max x (list_max xs)

def implementation (numbers: List Rat): List Rat :=
  if numbers.length < 2 then numbers
  else
    let min_elem := list_min numbers
    let max_elem := list_max numbers
    let range := max_elem - min_elem
    if min_elem = max_elem then
      numbers.map (fun _ => 0)
    else
      numbers.map (fun x => (x - min_elem) / range)

def problem_spec
-- function signature
(implementation: List Rat → List Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: List Rat) :=
2 ≤ numbers.length →
let min_elem := numbers.min?.get!;
let max_elem := numbers.max?.get!;
let range := max_elem - min_elem;
result.length = numbers.length ∧
∀ i, i < numbers.length →
(min_elem ≠ max_elem →
result[i]! = (numbers[i]! - min_elem) / range) ∧
(min_elem = max_elem →
result[i]! = 0);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma list_min_mem (l : List Rat) (h : l ≠ []) : list_min l ∈ l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp [list_min]
    cases' xs with y ys
    · simp
    · simp [min_def]
      split_ifs with h_cond
      · left; exact h_cond
      · right; exact ih (by simp)

-- LLM HELPER
lemma list_max_mem (l : List Rat) (h : l ≠ []) : list_max l ∈ l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp [list_max]
    cases' xs with y ys
    · simp
    · simp [max_def]
      split_ifs with h_cond
      · left; exact h_cond
      · right; exact ih (by simp)

-- LLM HELPER
lemma list_min_le (l : List Rat) (x : Rat) (h : x ∈ l) : list_min l ≤ x := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp [list_min]
    cases' ys with z zs
    · simp at h; rw [h]
    · simp at h
      cases h with
      | inl h_eq => rw [h_eq]; exact min_le_left _ _
      | inr h_mem => exact le_trans (min_le_right _ _) (ih h_mem)

-- LLM HELPER
lemma le_list_max (l : List Rat) (x : Rat) (h : x ∈ l) : x ≤ list_max l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp [list_max]
    cases' ys with z zs
    · simp at h; rw [h]
    · simp at h
      cases h with
      | inl h_eq => rw [h_eq]; exact le_max_left _ _
      | inr h_mem => exact le_trans (ih h_mem) (le_max_right _ _)

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    simp [implementation]
    have h_not_empty : numbers ≠ [] := by
      intro h_empty
      rw [h_empty] at h_len
      simp at h_len
    split_ifs with h_short
    · omega
    · simp
      constructor
      · simp [List.length_map]
      · intro i h_i
        simp [List.getElem_map]
        constructor
        · intro h_neq
          simp
        · intro h_eq
          simp