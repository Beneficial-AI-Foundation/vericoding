/- 
function_signature: "def pluck(numbers: List[Int]) -> List[Int]"
docstring: |
    Given an array representing a branch of a tree that has non-negative integer nodes
    your task is to pluck one of the nodes and return it.
    The plucked node should be the node with the smallest even value.
    If multiple nodes with the same smallest even value are found return the node that has smallest index.

    The plucked node should be returned in a list, [ smallest_value, its index ],
    If there are no even values or the given array is empty, return [].
test_cases:
  - input: [4, 2, 3]
    expected_output: [2, 1]
  - input: [1, 2, 3]
    expected_output: [2, 1]
  - input: []
    expected_output: []
  - input: [5, 0, 3, 0, 4, 2]
    expected_output: [0, 1]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def find_min_even_index (numbers: List Nat) : Option Nat :=
  let evens_with_indices := numbers.mapIdx (fun i x => (x, i)) |>.filter (fun (x, _) => x % 2 = 0)
  if evens_with_indices.isEmpty then 
    none 
  else 
    let min_val := evens_with_indices.map (fun (x, _) => x) |>.foldl min (evens_with_indices.head!.1)
    let candidates := evens_with_indices.filter (fun (x, _) => x = min_val)
    some (candidates.map (fun (_, i) => i) |>.foldl min (candidates.head!.2))

def implementation (numbers: List Nat) : List Nat :=
  match find_min_even_index numbers with
  | none => []
  | some idx => [numbers[idx]!, idx]

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(numbers: List Nat) :=
-- spec
let spec (result: List Nat) :=
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]! % 2 = 0 ∧
  result[0]! = numbers[i]! ∧
  result[1]! = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma find_min_even_index_none_iff_no_evens (numbers: List Nat) :
  find_min_even_index numbers = none ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1 := by
  constructor
  · intro h i hi
    by_contra h_even
    simp [find_min_even_index] at h
    have evens_nonempty : ¬(numbers.mapIdx (fun i x => (x, i)) |>.filter (fun (x, _) => x % 2 = 0)).isEmpty := by
      simp [List.isEmpty_iff_length_eq_zero]
      rw [List.length_pos_iff_exists_mem]
      use (numbers[i]!, i)
      simp [List.mem_filter, List.mem_mapIdx]
      use i, hi
      rw [Nat.mod_two_ne_one] at h_even
      exact h_even
    simp [if_neg evens_nonempty] at h
  · intro h
    simp [find_min_even_index]
    have evens_empty : (numbers.mapIdx (fun i x => (x, i)) |>.filter (fun (x, _) => x % 2 = 0)).isEmpty := by
      simp [List.isEmpty_iff_length_eq_zero, List.length_eq_zero_iff]
      intro ⟨x, i⟩
      simp [List.mem_filter, List.mem_mapIdx]
      intro j hj_lt hx_eq hi_eq heven
      rw [← hx_eq] at heven
      have := h j hj_lt
      rw [Nat.mod_two_ne_zero] at this
      rw [Nat.mod_two_eq_zero] at heven
      exact this heven
    simp [if_pos evens_empty]

-- LLM HELPER  
lemma find_min_even_index_some_correct (numbers: List Nat) (idx: Nat) :
  find_min_even_index numbers = some idx →
  idx < numbers.length ∧
  numbers[idx]! % 2 = 0 ∧
  (∀ j, j < numbers.length → j < idx → (numbers[j]! % 2 = 1 ∨ numbers[idx]! < numbers[j]!)) ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[idx]! ≤ numbers[k]!) := by
  intro h
  constructor
  · have : ∃ i, i < numbers.length ∧ numbers[i]! % 2 = 0 := by
      by_contra h_no_evens
      push_neg at h_no_evens
      have : find_min_even_index numbers = none := (find_min_even_index_none_iff_no_evens numbers).mpr h_no_evens
      rw [this] at h
      simp at h
    obtain ⟨i, hi_lt, _⟩ := this
    exact hi_lt
  constructor
  · have : ¬(∀ i, i < numbers.length → numbers[i]! % 2 = 1) := by
      intro h_all_odd
      have : find_min_even_index numbers = none := (find_min_even_index_none_iff_no_evens numbers).mpr h_all_odd
      rw [this] at h
      simp at h
    push_neg at this
    obtain ⟨i, hi_lt, hi_even⟩ := this
    rw [Nat.mod_two_ne_one] at hi_even
    exact hi_even
  constructor
  · intros j hj_lt hj_idx
    by_cases h_even : numbers[j]! % 2 = 0
    · right
      simp [find_min_even_index] at h
      split at h
      · simp at h
      · simp at h
        sorry
    · left
      rw [Nat.mod_two_ne_zero] at h_even
      exact h_even
  · intros k hk_lt hk_even
    simp [find_min_even_index] at h
    split at h
    · simp at h
    · simp at h
      sorry

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · unfold implementation
    cases h : find_min_even_index numbers with
    | none =>
      constructor
      · constructor
        · intro h_len
          simp [h] at h_len
          exact (find_min_even_index_none_iff_no_evens numbers).mp h
        · intro h_all_odd
          have : find_min_even_index numbers = none := (find_min_even_index_none_iff_no_evens numbers).mpr h_all_odd
          rw [this, h]
          simp
      · constructor
        · intro h_len
          simp [h] at h_len
        · intro ⟨i, hi_lt, hi_even, _, _, _, _⟩
          have := (find_min_even_index_none_iff_no_evens numbers).mp h i hi_lt
          rw [Nat.mod_two_ne_zero] at this
          exact this hi_even
    | some idx =>
      constructor
      · constructor
        · intro h_len
          simp [h] at h_len
        · intro h_all_odd
          have : find_min_even_index numbers = none := (find_min_even_index_none_iff_no_evens numbers).mpr h_all_odd
          simp [this] at h
      · constructor  
        · intro h_len
          simp [h] at h_len
          use idx
          have props := find_min_even_index_some_correct numbers idx h
          exact ⟨props.1, props.2.1, rfl, rfl, props.2.2.1, props.2.2.2⟩
        · intro ⟨i, hi_lt, hi_even, h_eq0, h_eq1, h_min_idx, h_min_val⟩
          simp [h]

-- #test implementation [4, 2, 3] = [2, 1]
-- #test implementation [1, 2, 3] = [2, 1]
-- #test implementation [] = []
-- #test implementation [5, 0, 3, 0, 4, 2] = [0, 1]