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
    cases' xs with y ys
    · simp [list_min]
    · simp [list_min]
      by_cases h_le : x ≤ list_min (y :: ys)
      · simp [min_def, h_le]
      · simp [min_def, h_le]
        right
        exact ih (by simp)

-- LLM HELPER
lemma list_max_mem (l : List Rat) (h : l ≠ []) : list_max l ∈ l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases' xs with y ys
    · simp [list_max]
    · simp [list_max]
      by_cases h_ge : list_max (y :: ys) ≤ x
      · simp [max_def, h_ge]
      · simp [max_def, h_ge]
        right
        exact ih (by simp)

-- LLM HELPER
lemma list_min_le (l : List Rat) (x : Rat) (h : x ∈ l) : list_min l ≤ x := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    cases' ys with z zs
    · simp at h
      simp [list_min, h]
    · simp [list_min]
      simp at h
      cases h with
      | inl h_eq => 
        rw [h_eq]
        exact min_le_left _ _
      | inr h_mem => 
        exact le_trans (min_le_right _ _) (ih h_mem)

-- LLM HELPER
lemma le_list_max (l : List Rat) (x : Rat) (h : x ∈ l) : x ≤ list_max l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    cases' ys with z zs
    · simp at h
      simp [list_max, h]
    · simp [list_max]
      simp at h
      cases h with
      | inl h_eq => 
        rw [h_eq]
        exact le_max_left _ _
      | inr h_mem => 
        exact le_trans (ih h_mem) (le_max_right _ _)

-- LLM HELPER
lemma list_min_eq_min_option (l : List Rat) (h : l ≠ []) : 
  l.min? = some (list_min l) := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases' xs with y ys
    · simp [list_min, List.min?]
    · simp [list_min, List.min?]
      have h_nonempty : y :: ys ≠ [] := by simp
      rw [ih h_nonempty]
      simp

-- LLM HELPER  
lemma list_max_eq_max_option (l : List Rat) (h : l ≠ []) : 
  l.max? = some (list_max l) := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    cases' xs with y ys
    · simp [list_max, List.max?]
    · simp [list_max, List.max?]
      have h_nonempty : y :: ys ≠ [] := by simp
      rw [ih h_nonempty]
      simp

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    have h_not_empty : numbers ≠ [] := by
      intro h_empty
      rw [h_empty] at h_len
      simp at h_len
    simp [implementation]
    split_ifs with h_short
    · omega
    · push_neg at h_short
      have h_min_eq : numbers.min?.get! = list_min numbers := by
        rw [list_min_eq_min_option numbers h_not_empty]
        simp
      have h_max_eq : numbers.max?.get! = list_max numbers := by
        rw [list_max_eq_max_option numbers h_not_empty]
        simp
      rw [h_min_eq, h_max_eq]
      split_ifs with h_eq
      · simp [List.length_map]
        constructor
        · rfl
        · intro i h_i
          simp [List.getElem_map, h_eq]
      · simp [List.length_map]
        constructor
        · rfl
        · intro i h_i
          simp [List.getElem_map]
          constructor
          · intro h_neq
            rfl
          · intro h_eq_contra
            contradiction