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
  constructor
  · exact List.sorted_insertionSort
  · simp [List.toFinset_insertionSort]

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
  have h_mem : ((lst.toFinset.toList).insertionSort (· ≤ ·))[i] ∈ (lst.toFinset.toList).insertionSort (· ≤ ·) := by
    rw [List.get_mem]
    exact hi
  rw [sorted_mem_iff] at h_mem
  simp [List.get!_eq_get] at h_mem
  exact h_mem

-- LLM HELPER
lemma sorted_get_le (lst : List Int) (i j : Nat) 
  (hi : i < (lst.toFinset.toList).insertionSort (· ≤ ·).length)
  (hj : j < (lst.toFinset.toList).insertionSort (· ≤ ·).length)
  (hij : i < j) :
  ((lst.toFinset.toList).insertionSort (· ≤ ·))[i]! ≤ ((lst.toFinset.toList).insertionSort (· ≤ ·))[j]! := by
  have h_sorted := (sorted_properties lst).1
  have : ((lst.toFinset.toList).insertionSort (· ≤ ·))[i] ≤ ((lst.toFinset.toList).insertionSort (· ≤ ·))[j] := 
    List.Sorted.getElem_le h_sorted hij
  simp only [List.get!_eq_get, List.get_eq_getElem] at this
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
    · constructor
      · -- Show 0 < (lst.filter (· < sorted[1]!)).length
        have h_len : 2 ≤ sorted.length := h
        have h0_lt : 0 < sorted.length := by omega
        have h1_lt : 1 < sorted.length := by omega
        
        -- Show that sorted[0]! < sorted[1]! (they must be distinct in a finset)
        have h_distinct : sorted[0]! ≠ sorted[1]! := by
          by_contra h_eq
          have mem0 : sorted[0] ∈ sorted := List.get_mem _ _ h0_lt
          have mem1 : sorted[1] ∈ sorted := List.get_mem _ _ h1_lt
          simp [List.get!_eq_get] at h_eq
          have : sorted[0] = sorted[1] := by rw [List.get_eq_getElem, List.get_eq_getElem]; exact h_eq
          have : (0 : Fin sorted.length) = (1 : Fin sorted.length) := by
            apply List.nodup_iff_get_ne_get.mp _ this
            · rw [List.nodup_toList, ←List.toFinset_insertionSort]
              exact Finset.nodup_toList _
            · norm_num
          norm_num at this
        
        have h_lt : sorted[0]! < sorted[1]! := 
          lt_of_le_of_ne (sorted_get_le lst 0 1 h0_lt h1_lt (by norm_num)) h_distinct
        
        have h_mem : sorted[0]! ∈ lst := get_mem_original lst 0 h0_lt
        have h_filter : sorted[0]! ∈ lst.filter (· < sorted[1]!) := by
          rw [List.mem_filter]
          constructor
          · exact h_mem
          · simp [h_lt]
        exact List.length_pos_of_mem h_filter
      
      · -- Show all elements in smaller_els are equal
        intro y hy
        have hy_prop := List.mem_filter.mp hy
        have hy_mem : y ∈ lst := hy_prop.1
        have hy_lt : y < sorted[1]! := by
          simp at hy_prop
          exact hy_prop.2
        
        -- y must be in sorted list
        have y_in_sorted : y ∈ sorted := by
          rw [sorted_mem_iff]
          exact hy_mem
        
        -- Since sorted is sorted and y < sorted[1]!, y must equal sorted[0]!
        have y_eq_first : y = sorted[0]! := by
          obtain ⟨k, hk_bound, hk_eq⟩ := List.mem_iff_get.mp y_in_sorted
          have : k = 0 := by
            by_contra hk_ne
            have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
            cases' Nat.eq_or_lt_of_le hk_pos with h_one h_ge_one
            · -- k = 1
              rw [h_one] at hk_eq
              simp [List.get!_eq_get, List.get_eq_getElem] at hk_eq
              rw [hk_eq] at hy_lt
              exact lt_irrefl _ hy_lt
            · -- k > 1
              have h1_lt : 1 < sorted.length := by omega
              have : sorted[1]! ≤ sorted[k]! := sorted_get_le lst 1 k h1_lt hk_bound h_ge_one
              simp [List.get!_eq_get, List.get_eq_getElem] at this hk_eq
              rw [←hk_eq] at this
              exact not_le.mpr hy_lt this
          rw [this] at hk_eq
          simp [List.get!_eq_get, List.get_eq_getElem] at hk_eq
          exact hk_eq.symm
        
        -- Show smaller_els[0]! = sorted[0]!
        have smaller_first : (lst.filter (· < sorted[1]!))[0]! = sorted[0]! := by
          have sorted0_in_filter : sorted[0]! ∈ lst.filter (· < sorted[1]!) := by
            have h0_lt : 0 < sorted.length := by omega
            have h1_lt : 1 < sorted.length := by omega
            have h_lt : sorted[0]! < sorted[1]! := by
              have h_distinct : sorted[0]! ≠ sorted[1]! := by
                by_contra h_eq
                have : (0 : Fin sorted.length) = (1 : Fin sorted.length) := by
                  apply List.nodup_iff_get_ne_get.mp _ 
                  · rw [List.nodup_toList, ←List.toFinset_insertionSort]
                    exact Finset.nodup_toList _
                  · simp [List.get!_eq_get, List.get_eq_getElem] at h_eq
                    exact h_eq
                  · norm_num
                norm_num at this
              exact lt_of_le_of_ne (sorted_get_le lst 0 1 h0_lt h1_lt (by norm_num)) h_distinct
            rw [List.mem_filter]
            constructor
            · exact get_mem_original lst 0 h0_lt
            · simp [h_lt]
          have pos_len : 0 < (lst.filter (· < sorted[1]!)).length := List.length_pos_of_mem sorted0_in_filter
          have : (lst.filter (· < sorted[1]!))[0]! ∈ lst.filter (· < sorted[1]!) := List.get!_mem _ 0
          have this_prop := List.mem_filter.mp this
          have : (lst.filter (· < sorted[1]!))[0]! < sorted[1]! := by
            simp at this_prop
            exact this_prop.2
          have first_in_sorted : (lst.filter (· < sorted[1]!))[0]! ∈ sorted := by
            rw [sorted_mem_iff]
            exact this_prop.1
          -- Same argument as for y
          obtain ⟨k, hk_bound, hk_eq⟩ := List.mem_iff_get.mp first_in_sorted
          have k_zero : k = 0 := by
            by_contra hk_ne
            have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
            cases' Nat.eq_or_lt_of_le hk_pos with h_one h_ge_one
            · rw [h_one] at hk_eq
              simp [List.get!_eq_get, List.get_eq_getElem] at hk_eq
              rw [hk_eq] at this
              exact lt_irrefl _ this
            · have h1_lt : 1 < sorted.length := by omega
              have : sorted[1]! ≤ sorted[k]! := sorted_get_le lst 1 k h1_lt hk_bound h_ge_one
              simp [List.get!_eq_get, List.get_eq_getElem] at this hk_eq
              rw [←hk_eq] at this
              exact not_le.mpr this this
          rw [k_zero] at hk_eq
          simp [List.get!_eq_get, List.get_eq_getElem] at hk_eq
          exact hk_eq.symm
        
        rw [smaller_first, y_eq_first]
  
  · -- Case: sorted.length < 2
    use none
    constructor
    · simp only [h, ite_false]
    · push_neg at h ⊢
      simp only [not_exists]
      intro i j hi hj hij
      
      -- If there exist distinct positions, then sorted.length ≥ 2
      have i_mem : lst[i]! ∈ lst.toFinset := List.mem_toFinset.mpr (List.get!_mem lst i)
      have j_mem : lst[j]! ∈ lst.toFinset := List.mem_toFinset.mpr (List.get!_mem lst j)
      
      have sorted_len : sorted.length = lst.toFinset.card := List.length_toList _
      rw [sorted_len] at h
      
      -- If lst[i]! < lst[j]!, they are distinct
      intro hlt
      have distinct : lst[i]! ≠ lst[j]! := ne_of_lt hlt
      
      have card_ge_two : 2 ≤ lst.toFinset.card := by
        have : ({lst[i]!, lst[j]!} : Finset Int).card = 2 := by
          rw [Finset.card_pair distinct]
        rw [←this]
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        cases hx with
        | inl h_eq => rw [h_eq]; exact i_mem
        | inr h_eq => rw [h_eq]; exact j_mem
      
      exact not_le.mpr card_ge_two h