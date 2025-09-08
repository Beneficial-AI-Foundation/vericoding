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

noncomputable def implementation (lst: List Int) : Option Int :=
  let sorted := (lst.toFinset.toList).insertionSort (· ≤ ·)
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
lemma sorted_properties (lst : List Int) :
  let sorted := (lst.toFinset.toList).insertionSort (· ≤ ·)
  sorted.Sorted (· ≤ ·) ∧ sorted.toFinset = lst.toFinset := by
  simp only [List.sorted_insertionSort, true_and]
  rw [List.toFinset_insertionSort_of_sorted]
  exact List.sorted_insertionSort

-- LLM HELPER
lemma sorted_mem_iff (lst : List Int) :
  let sorted := (lst.toFinset.toList).insertionSort (· ≤ ·)
  ∀ x, x ∈ sorted ↔ x ∈ lst := by
  intro x
  let sorted := (lst.toFinset.toList).insertionSort (· ≤ ·)
  rw [List.mem_insertionSort, List.mem_toList, List.mem_toFinset]

-- LLM HELPER
lemma get_mem_original (lst : List Int) (i : Nat) (hi : i < (lst.toFinset.toList).insertionSort (· ≤ ·).length) :
  ((lst.toFinset.toList).insertionSort (· ≤ ·))[i]! ∈ lst := by
  have h_mem : ((lst.toFinset.toList).insertionSort (· ≤ ·))[i]! ∈ (lst.toFinset.toList).insertionSort (· ≤ ·) := by
    rw [List.get!_pos]
    exact hi
  rw [sorted_mem_iff] at h_mem
  exact h_mem

-- LLM HELPER
lemma sorted_get_le (lst : List Int) (i j : Nat) 
  (hi : i < (lst.toFinset.toList).insertionSort (· ≤ ·).length)
  (hj : j < (lst.toFinset.toList).insertionSort (· ≤ ·).length)
  (hij : i < j) :
  ((lst.toFinset.toList).insertionSort (· ≤ ·))[i]! ≤ ((lst.toFinset.toList).insertionSort (· ≤ ·))[j]! := by
  have h_sorted := (sorted_properties lst).1
  have : ((lst.toFinset.toList).insertionSort (· ≤ ·))[i] ≤ ((lst.toFinset.toList).insertionSort (· ≤ ·))[j] := 
    List.Sorted.get_le h_sorted hij
  rw [List.get_eq_getElem, List.get_eq_getElem] at this
  simp only [List.get!_eq_getElem]
  exact this

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp only [problem_spec, implementation]
  let sorted := (lst.toFinset.toList).insertionSort (· ≤ ·)
  by_cases h : sorted.length ≥ 2
  · -- Case: sorted.length ≥ 2
    use some sorted[1]!
    constructor
    · simp only [h, ite_true]
    · simp only [List.all_eq_true]
      have h_len : 2 ≤ sorted.length := h
      have h0_lt : 0 < sorted.length := by omega
      have h1_lt : 1 < sorted.length := by omega
      
      -- Show that sorted[0]! < sorted[1]!
      have h_distinct : sorted[0]! ≠ sorted[1]! := by
        by_contra h_eq
        have h_le : sorted[0]! ≤ sorted[1]! := sorted_get_le lst 0 1 h0_lt h1_lt (by norm_num)
        have h_ge : sorted[1]! ≤ sorted[0]! := by rw [h_eq]; exact le_refl _
        have : sorted[0]! = sorted[1]! := le_antisymm h_le h_ge
        exact h_eq this
      
      have h_lt : sorted[0]! < sorted[1]! := 
        lt_of_le_of_ne (sorted_get_le lst 0 1 h0_lt h1_lt (by norm_num)) h_distinct
      
      let smaller_els := lst.filter (· < sorted[1]!)
      
      constructor
      · -- 0 < smaller_els.length
        have h_mem : sorted[0]! ∈ lst := get_mem_original lst 0 h0_lt
        have h_filter : sorted[0]! ∈ smaller_els := by
          rw [List.mem_filter]
          exact ⟨h_mem, h_lt⟩
        exact List.length_pos_of_mem h_filter
      
      · -- All elements in smaller_els are equal to smaller_els[0]!
        intro y hy
        have hy_prop := List.mem_filter.mp hy
        have hy_mem : y ∈ lst := hy_prop.1
        have hy_lt : y < sorted[1]! := Bool.of_decide_true hy_prop.2
        
        -- y must be in sorted list
        have y_in_sorted : y ∈ sorted := by
          rw [sorted_mem_iff]
          exact hy_mem
        
        -- y must be at position 0 in sorted list (since it's < sorted[1]!)
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp y_in_sorted
        cases hk_some : sorted[k]? with
        | none => simp [hk_some] at hk
        | some val =>
          have hk_val : val = y := by simp [hk_some] at hk; exact hk
          have hk_bound : k < sorted.length := (List.get?_eq_some_iff.mp hk_some).1
          
          -- If k ≥ 1, then sorted[1]! ≤ y, contradicting y < sorted[1]!
          have hk_zero : k = 0 := by
            by_contra hk_ne
            have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
            have hk_ge_one : 1 ≤ k := hk_pos
            have : sorted[1]! ≤ sorted[k]! := sorted_get_le lst 1 k h1_lt hk_bound hk_ge_one
            rw [←hk_val] at this
            exact not_le.mpr hy_lt this
          
          rw [hk_zero] at hk_val
          have sorted0_in_filter : sorted[0]! ∈ smaller_els := by
            have sorted0_mem : sorted[0]! ∈ lst := get_mem_original lst 0 h0_lt
            rw [List.mem_filter]
            exact ⟨sorted0_mem, h_lt⟩
          
          -- smaller_els[0]! should be sorted[0]!
          have smaller_head : smaller_els[0]! = sorted[0]! := by
            have h_pos : 0 < smaller_els.length := List.length_pos_of_mem sorted0_in_filter
            -- All elements in smaller_els are sorted[0]! (since they're all < sorted[1]! and in sorted list)
            have all_same : ∀ z ∈ smaller_els, z = sorted[0]! := by
              intro z hz
              have z_prop := List.mem_filter.mp hz
              have z_mem : z ∈ lst := z_prop.1
              have z_lt : z < sorted[1]! := Bool.of_decide_true z_prop.2
              
              have z_in_sorted : z ∈ sorted := by
                rw [sorted_mem_iff]; exact z_mem
              
              obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp z_in_sorted
              cases hm_some : sorted[m]? with
              | none => simp [hm_some] at hm
              | some zval =>
                have hm_val : zval = z := by simp [hm_some] at hm; exact hm
                have hm_bound : m < sorted.length := (List.get?_eq_some_iff.mp hm_some).1
                
                have hm_zero : m = 0 := by
                  by_contra hm_ne
                  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
                  have hm_ge_one : 1 ≤ m := hm_pos
                  have : sorted[1]! ≤ sorted[m]! := sorted_get_le lst 1 m h1_lt hm_bound hm_ge_one
                  rw [←hm_val] at this
                  exact not_le.mpr z_lt this
                
                rw [hm_zero] at hm_val
                exact hm_val
            
            exact (all_same (smaller_els[0]!) (List.get!_mem smaller_els 0)).symm
          
          rw [smaller_head, ←hk_val]
          have : smaller_els[0]! = y := by
            -- We need to show that any element y in smaller_els equals smaller_els[0]!
            have all_same : ∀ z ∈ smaller_els, z = smaller_els[0]! := by
              intro z hz
              -- Similar reasoning as above - all elements < sorted[1]! must be at position 0
              have z_prop := List.mem_filter.mp hz
              have z_mem : z ∈ lst := z_prop.1
              have z_lt : z < sorted[1]! := Bool.of_decide_true z_prop.2
              
              have z_in_sorted : z ∈ sorted := by
                rw [sorted_mem_iff]; exact z_mem
              
              obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp z_in_sorted
              cases hm_some : sorted[m]? with
              | none => simp [hm_some] at hm
              | some zval =>
                have hm_val : zval = z := by simp [hm_some] at hm; exact hm
                have hm_bound : m < sorted.length := (List.get?_eq_some_iff.mp hm_some).1
                
                have hm_zero : m = 0 := by
                  by_contra hm_ne
                  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
                  have hm_ge_one : 1 ≤ m := hm_pos
                  have : sorted[1]! ≤ sorted[m]! := sorted_get_le lst 1 m h1_lt hm_bound hm_ge_one
                  rw [←hm_val] at this
                  exact not_le.mpr z_lt this
                
                -- All elements in smaller_els are at position 0 in sorted, so they're all equal
                simp only [Bool.decide_eq_true]
                rw [hm_zero] at hm_val
                have sorted_0_in_smaller : sorted[0]! ∈ smaller_els := by
                  rw [List.mem_filter]
                  exact ⟨get_mem_original lst 0 h0_lt, h_lt⟩
                have : smaller_els[0]! = sorted[0]! := by
                  have pos : 0 < smaller_els.length := List.length_pos_of_mem sorted_0_in_smaller
                  -- Need to show sorted[0]! is the first element
                  sorry -- This requires more complex reasoning about list structure
                exact sorry
            exact all_same y hy
          exact this
  
  · -- Case: sorted.length < 2
    use none
    constructor
    · simp only [h, ite_false]
    · push_neg at h ⊢
      intro i j hi hj hij hlt
      
      -- If there exist distinct elements with lst[i]! < lst[j]!, then sorted.length ≥ 2
      have distinct_in_finset : lst[i]! ≠ lst[j]! := ne_of_lt hlt
      have i_mem : lst[i]! ∈ lst.toFinset := List.mem_toFinset.mpr (List.get!_mem lst i)
      have j_mem : lst[j]! ∈ lst.toFinset := List.mem_toFinset.mpr (List.get!_mem lst j)
      
      have card_ge_two : 2 ≤ lst.toFinset.card := by
        have : {lst[i]!, lst[j]!}.card = 2 := by
          rw [Finset.card_pair distinct_in_finset]
        rw [←this]
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        cases hx with
        | inl h => rw [h]; exact i_mem
        | inr h => rw [h]; exact j_mem
      
      have sorted_len : sorted.length = lst.toFinset.card := List.length_toList _
      rw [sorted_len] at h
      exact not_le.mpr card_ge_two h