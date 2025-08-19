import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int → List Int)
-- inputs
(l1 l2: List Int) :=
let is_unique (result: List Int) :=
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]!;
let is_sorted (result: List Int) :=
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]!;
-- spec
let spec (result: List Int) :=
  is_unique result ∧
  is_sorted result ∧
  (∀ i : Int, i ∈ result ↔ i ∈ l1 ∧ i ∈ l2)
-- program termination
∃ result, implementation l1 l2 = result ∧
spec result

-- LLM HELPER
def intersection (l1 l2: List Int) : List Int :=
  l1.filter (fun x => x ∈ l2)

-- LLM HELPER
def merge_sort (l: List Int) : List Int :=
  match l with
  | [] => []
  | [x] => [x]
  | _ => 
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    let sorted_left := merge_sort left
    let sorted_right := merge_sort right
    merge sorted_left sorted_right
where
  merge (l1 l2: List Int) : List Int :=
    match l1, l2 with
    | [], l2 => l2
    | l1, [] => l1
    | x::xs, y::ys => 
      if x ≤ y then x :: merge xs (y::ys)
      else y :: merge (x::xs) ys

-- LLM HELPER
def remove_duplicates (l: List Int) : List Int :=
  match l with
  | [] => []
  | x::xs => 
    if x ∈ xs then remove_duplicates xs
    else x :: remove_duplicates xs

def implementation (l1 l2: List Int) : List Int := 
  remove_duplicates (merge_sort (intersection l1 l2))

-- LLM HELPER
lemma intersection_mem (l1 l2: List Int) (x: Int) : x ∈ intersection l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  simp [intersection, List.mem_filter]

-- LLM HELPER
lemma merge_sort_mem (l: List Int) (x: Int) : x ∈ merge_sort l ↔ x ∈ l := by
  sorry

-- LLM HELPER
lemma merge_sort_sorted (l: List Int) : 
  ∀ i, i < (merge_sort l).length - 1 → (merge_sort l)[i]! ≤ (merge_sort l)[i + 1]! := by
  sorry

-- LLM HELPER
lemma remove_duplicates_mem (l: List Int) (x: Int) : x ∈ remove_duplicates l ↔ x ∈ l := by
  sorry

-- LLM HELPER
lemma remove_duplicates_unique (l: List Int) : 
  ∀ i j, i < (remove_duplicates l).length → j < (remove_duplicates l).length →
  i ≠ j → (remove_duplicates l)[i]! ≠ (remove_duplicates l)[j]! := by
  sorry

-- LLM HELPER
lemma remove_duplicates_preserves_sorted (l: List Int) : 
  (∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) →
  (∀ i, i < (remove_duplicates l).length - 1 → (remove_duplicates l)[i]! ≤ (remove_duplicates l)[i + 1]!) := by
  sorry

theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2
:= by
  simp [problem_spec, implementation]
  use remove_duplicates (merge_sort (intersection l1 l2))
  constructor
  · rfl
  · constructor
    · -- is_unique
      exact remove_duplicates_unique (merge_sort (intersection l1 l2))
    · constructor
      · -- is_sorted
        apply remove_duplicates_preserves_sorted
        exact merge_sort_sorted (intersection l1 l2)
      · -- membership equivalence
        intro i
        constructor
        · intro h
          rw [remove_duplicates_mem] at h
          rw [merge_sort_mem] at h
          rw [intersection_mem] at h
          exact h
        · intro h
          rw [remove_duplicates_mem]
          rw [merge_sort_mem]
          rw [intersection_mem]
          exact h