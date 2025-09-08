/- 
function_signature: "def next_smallest(lst: List[int]) -> Optional[int]"
docstring: |
    You are given a list of integers.
    Write a function next_smallest() that returns the 2nd smallest element of the list.
    Return None if there is no such element.
    TODO(George): Remove this when being reviewed
    The spec is defined as: if result is none there is no second smallest element, which
    exists in a finite list iff there are at least two distinct elements in the list.
    If result is some x, then x is the second smallest element of the list, the spec
    obtains the sublist of elements smaller than the result, and checks that this
    sublist does not contain two distinct elements (they are all the same).
test_cases:
  - input: [1, 2, 3, 4, 5]
    output: 2
  - input: [5, 1, 4, 3, 2]
    output: 2
  - input: []
    output: None
  - input: [1, 1]
    output: None
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Int) : Option Int :=
  let sorted := lst.toFinset.toList.insertionSort (· ≤ ·)
  if sorted.length ≥ 2 then some sorted[1]! else none

def problem_spec
-- function signature
(implementation: List Int → Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Option Int) :=
  match result with
  | none => ¬ (∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst[i]! < lst[j]!)
  | some result =>
    let smaller_els := lst.filter (· < result);
    0 < smaller_els.length ∧
    smaller_els.all (λ x => x = smaller_els[0]!);
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
lemma sorted_distinct_elements (lst : List Int) :
  let sorted := lst.toFinset.toList.insertionSort (· ≤ ·)
  sorted.length ≥ 2 → ∃ i j, i < lst.length ∧ j < lst.length ∧ i ≠ j ∧ lst[i]! < lst[j]! := by
  intro h
  let sorted := lst.toFinset.toList.insertionSort (· ≤ ·)
  have h1 : sorted[0]! < sorted[1]! := by
    have h_sorted : sorted.Sorted (· ≤ ·) := List.sorted_insertionSort (· ≤ ·) _
    have h_len : 2 ≤ sorted.length := h
    have h_distinct : sorted[0]! ≠ sorted[1]! := by
      by_contra h_eq
      have h_le : sorted[0]! ≤ sorted[1]! := List.Sorted.get_le h_sorted (by norm_num) (by norm_num : 0 < 1)
      have h_ge : sorted[1]! ≤ sorted[0]! := by rw [h_eq]
      have h_eq' : sorted[0]! = sorted[1]! := le_antisymm h_le h_ge
      contradiction
    exact lt_of_le_of_ne (List.Sorted.get_le h_sorted (by norm_num) (by norm_num : 0 < 1)) h_distinct
  have h2 : sorted[0]! ∈ lst := by
    have : sorted[0]! ∈ sorted := List.get_mem _ _ _
    have : sorted ⊆ lst := by
      intro x hx
      have : x ∈ lst.toFinset := by
        rw [List.mem_toFinset] at hx ⊢
        exact List.mem_of_mem_insertionSort hx
      exact List.mem_toFinset.mp this
    exact this this
  have h3 : sorted[1]! ∈ lst := by
    have : sorted[1]! ∈ sorted := List.get_mem _ _ _
    have : sorted ⊆ lst := by
      intro x hx
      have : x ∈ lst.toFinset := by
        rw [List.mem_toFinset] at hx ⊢
        exact List.mem_of_mem_insertionSort hx
      exact List.mem_toFinset.mp this
    exact this this
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp h2
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h3
  use i, j
  exact ⟨i.isLt, j.isLt, by simp [hi.symm, hj.symm, h1], by simp [hi.symm, hj.symm, h1]⟩

-- LLM HELPER  
lemma filter_all_same (lst : List Int) (x : Int) :
  let sorted := lst.toFinset.toList.insertionSort (· ≤ ·)
  sorted.length ≥ 2 → 
  x = sorted[1]! →
  let smaller_els := lst.filter (· < x)
  0 < smaller_els.length ∧ smaller_els.all (λ y => y = smaller_els[0]!) := by
  intro h_len h_eq
  let sorted := lst.toFinset.toList.insertionSort (· ≤ ·)  
  let smaller_els := lst.filter (· < x)
  constructor
  · -- 0 < smaller_els.length
    have h1 : sorted[0]! < x := by
      rw [h_eq]
      have h_sorted : sorted.Sorted (· ≤ ·) := List.sorted_insertionSort (· ≤ ·) _
      have h_distinct : sorted[0]! ≠ sorted[1]! := by
        by_contra h_eq_same
        have h_le : sorted[0]! ≤ sorted[1]! := List.Sorted.get_le h_sorted (by norm_num) (by norm_num : 0 < 1)
        have h_ge : sorted[1]! ≤ sorted[0]! := by rw [h_eq_same]
        have h_eq' : sorted[0]! = sorted[1]! := le_antisymm h_le h_ge
        contradiction
      exact lt_of_le_of_ne (List.Sorted.get_le h_sorted (by norm_num) (by norm_num : 0 < 1)) h_distinct
    have h2 : sorted[0]! ∈ lst := by
      have : sorted[0]! ∈ sorted := List.get_mem _ _ _
      have : sorted ⊆ lst := by
        intro y hy
        have : y ∈ lst.toFinset := by
          rw [List.mem_toFinset] at hy ⊢
          exact List.mem_of_mem_insertionSort hy
        exact List.mem_toFinset.mp this
      exact this this
    have h3 : sorted[0]! ∈ smaller_els := List.mem_filter.mpr ⟨h2, h1⟩
    exact List.length_pos_of_mem h3
  · -- smaller_els.all (λ y => y = smaller_els[0]!)
    simp [List.all_eq_true]
    intro y hy
    have hy_mem := List.mem_filter.mp hy
    have hy_lt : y < x := hy_mem.2
    rw [h_eq] at hy_lt
    -- y < sorted[1]!, and sorted[0]! is the unique minimum less than sorted[1]!
    have h_min : ∀ z ∈ lst, z < sorted[1]! → z = sorted[0]! := by
      intro z hz_mem hz_lt
      have hz_in_sorted : z ∈ sorted := by
        rw [List.mem_insertionSort]
        exact List.mem_toFinset.mpr hz_mem
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hz_in_sorted
      have h_sorted : sorted.Sorted (· ≤ ·) := List.sorted_insertionSort (· ≤ ·) _
      have hk_lt : z < sorted[1]! := hz_lt
      rw [←hk] at hk_lt
      have : k < 1 := by
        by_contra h_ge
        push_neg at h_ge
        have : 1 ≤ k := h_ge
        have : sorted[1]! ≤ sorted[k] := List.Sorted.get_le h_sorted (by norm_num) this
        rw [hk] at this
        exact not_le.mpr hk_lt this
      have : k = 0 := by
        cases k with
        | zero => rfl
        | succ k' => 
          simp at this
          exact False.elim this
      rw [this] at hk
      exact hk.symm
    have hy_eq : y = sorted[0]! := h_min y hy_mem.1 hy_lt
    have h_first : sorted[0]! ∈ smaller_els := by
      have h1 : sorted[0]! < x := by
        rw [h_eq]
        have h_sorted : sorted.Sorted (· ≤ ·) := List.sorted_insertionSort (· ≤ ·) _
        have h_distinct : sorted[0]! ≠ sorted[1]! := by
          by_contra h_eq_same
          have h_le : sorted[0]! ≤ sorted[1]! := List.Sorted.get_le h_sorted (by norm_num) (by norm_num : 0 < 1)  
          have h_ge : sorted[1]! ≤ sorted[0]! := by rw [h_eq_same]
          have h_eq' : sorted[0]! = sorted[1]! := le_antisymm h_le h_ge
          contradiction
        exact lt_of_le_of_ne (List.Sorted.get_le h_sorted (by norm_num) (by norm_num : 0 < 1)) h_distinct
      have h2 : sorted[0]! ∈ lst := by
        have : sorted[0]! ∈ sorted := List.get_mem _ _ _
        have : sorted ⊆ lst := by
          intro z hz
          have : z ∈ lst.toFinset := by
            rw [List.mem_toFinset] at hz ⊢
            exact List.mem_of_mem_insertionSort hz
          exact List.mem_toFinset.mp this
        exact this this
      exact List.mem_filter.mpr ⟨h2, h1⟩
    have h_first_is_head : smaller_els[0]! = sorted[0]! := by
      have h_nonempty : 0 < smaller_els.length := List.length_pos_of_mem h_first
      have h_all_same : ∀ z ∈ smaller_els, z = sorted[0]! := by
        intro z hz
        have hz_mem := List.mem_filter.mp hz
        exact h_min z hz_mem.1 (by rw [h_eq]; exact hz_mem.2)
      exact (h_all_same (smaller_els[0]!) (List.get_mem _ _ _)).symm
    rw [h_first_is_head, hy_eq]

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  simp [problem_spec, implementation]
  let sorted := lst.toFinset.toList.insertionSort (· ≤ ·)
  by_cases h : sorted.length ≥ 2
  · use some sorted[1]!
    simp [h]
    constructor
    · rfl
    · simp
      exact filter_all_same lst sorted[1]! h rfl
  · use none
    simp [h]
    constructor  
    · rfl
    · push_neg at h ⊢
      intro i j hi hj hij hlt
      have h_distinct : ∃ x y, x ∈ lst ∧ y ∈ lst ∧ x ≠ y := ⟨lst[i]!, lst[j]!, List.get_mem _ _ _, List.get_mem _ _ _, by simp [List.get_eq_iff]; exact fun h_eq => not_lt.mpr (le_of_eq h_eq.symm) hlt⟩
      have h_card : lst.toFinset.card ≥ 2 := by
        obtain ⟨x, y, hx_mem, hy_mem, hxy⟩ := h_distinct
        have : x ≠ y := hxy
        have hx_in : x ∈ lst.toFinset := List.mem_toFinset.mpr hx_mem
        have hy_in : y ∈ lst.toFinset := List.mem_toFinset.mpr hy_mem
        exact Finset.card_le_card_of_inj_on id (fun _ _ => id) 
          (Finset.inj_on_of_injective Function.injective_id _) 
          |>.trans_eq (Finset.card_image_of_injective {x, y} Function.injective_id) 
          |>.symm.trans_le (Finset.card_le_card (Finset.subset_iff.mpr fun z hz => by
            rw [Finset.mem_insert, Finset.mem_singleton] at hz
            cases hz with
            | inl h => rw [h]; exact hx_in  
            | inr h => rw [h]; exact hy_in))
          |>.trans_eq (Finset.card_insert_of_not_mem (Finset.not_mem_singleton.mpr hxy.symm))
          |>.trans_eq (Finset.card_singleton _)
          |>.symm.trans_le (by norm_num : 2 ≤ 2)
      have h_len : sorted.length = lst.toFinset.card := List.length_toList _
      rw [h_len] at h
      exact not_le.mpr h_card h

-- #test implementation [1, 2, 3, 4, 5] = some 2
-- #test implementation [5, 1, 4, 3, 2] = some 2  
-- #test implementation [] = none
-- #test implementation [1, 1] = none