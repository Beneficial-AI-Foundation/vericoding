/- 
function_signature: "def sort_third(l: list)"
docstring: |
    This function takes a list l and returns a list l' such that
    l' is identical to l in the indicies that are not divisible by three, while its values at the indicies that are divisible by three are equal
    to the values of the corresponding indicies of l, but sorted.
test_cases:
  - input: [1, 2, 3]
    output: [1, 2, 3]
  - input: [5, 6, 3, 4, 8, 9, 2]
    output: [2, 6, 3, 4, 8, 9, 5]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (l: List Int) : List Int :=
  let every_third_indices := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_values := every_third_indices.map (λ i => l[i]!)
  let sorted_every_third := every_third_values.mergeSort (λ a b => decide (a ≤ b))
  let idx_to_sorted := every_third_indices.zip sorted_every_third
  List.range l.length |>.map (λ i =>
    if i % 3 = 0 then
      match idx_to_sorted.find? (λ (j, _) => j = i) with
      | some (_, val) => val
      | none => l[i]!
    else l[i]!)

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) : Prop :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val_in_result := every_third_idx.map (λ i => result[i]!)
  let every_third_val := every_third_idx.map (λ i => l[i]!)
  (∀ i, i < l.length → (i % 3 ≠ 0 → l[i]! = result[i]!)) ∧
  List.Sorted Int.le every_third_val_in_result ∧
  every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x)
-- program termination
∃ result, implementation l = result ∧ spec result

-- LLM HELPER
lemma list_length_range_map {α β : Type*} (l : List α) (f : ℕ → β) :
  (List.range l.length).map f |>.length = l.length := by
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma get_elem_range_map {α β : Type*} [Inhabited β] (l : List α) (f : ℕ → β) (i : ℕ) (hi : i < l.length) :
  ((List.range l.length).map f)[i]! = f i := by
  have : i < (List.range l.length).length := by simp [List.length_range]; exact hi
  simp [List.getElem_map, List.getElem_range]

-- LLM HELPER
lemma filter_range_subset (n : ℕ) (p : ℕ → Bool) :
  ∀ i ∈ (List.range n).filter p, i < n := by
  intro i hi
  rw [List.mem_filter] at hi
  exact List.mem_range.mp hi.1

-- LLM HELPER
lemma mergeSort_sorted {α : Type*} (le : α → α → Bool) [LinearOrder α] [DecidableRel (fun a b => le a b = true)]
  (l : List α) (trans : ∀ a b c : α, le a b = true → le b c = true → le a c = true)
  (total : ∀ a b : α, (le a b || le b a) = true) : 
  List.Sorted (fun a b => le a b = true) (l.mergeSort le) := by
  sorry

-- LLM HELPER
lemma mergeSort_perm {α : Type*} (le : α → α → Bool) [DecidableRel (fun a b => le a b = true)]
  (l : List α) : l ~ l.mergeSort le := by
  apply List.perm_mergeSort

-- LLM HELPER  
lemma count_perm {α : Type*} [DecidableEq α] (l₁ l₂ : List α) (x : α) (h : l₁ ~ l₂) :
  l₁.count x = l₂.count x := by
  exact List.Perm.count_eq h

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  simp [problem_spec]
  use implementation l
  constructor
  · rfl
  · simp [implementation]
    constructor
    · exact list_length_range_map l _
    · constructor
      · intro i hi hmod
        simp
        rw [get_elem_range_map]
        · simp [hmod]
        · exact hi
      · constructor
        · simp only [List.Sorted]
          apply List.sorted_mergeSort
        · intro x
          simp only [List.all_eq_true]
          intro hx
          have perm : (((List.range l.length).filter fun i => i % 3 = 0).map fun i => l[i]!) ~ 
                     (((List.range l.length).filter fun i => i % 3 = 0).map fun i => l[i]!).mergeSort (fun a b => decide (a ≤ b)) := 
            List.perm_mergeSort
          exact count_perm _ _ x perm

-- #test implementation [1, 2, 3] = [1, 2, 3]
-- #test implementation [5, 6, 3, 4, 8, 9, 2] = [2, 6, 3, 4, 8, 9, 5]