import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0);
  let even_val_in_result := even_idx.map (λ i => result.get! i);
  let even_val := even_idx.map (λ i => l.get! i);
  (∀ i, i < l.length → (i % 2 ≠ 0 → l.get! i = result.get! i)) ∧
  List.Sorted Int.le even_val_in_result ∧
  even_val.all (λ x => even_val_in_result.count x = even_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
def get_even_indexed_elements (l: List Int) : List Int :=
  (List.range l.length).filter (λ i => i % 2 = 0) |>.map (λ i => l.get! i)

-- LLM HELPER
def set_even_indexed_elements (l: List Int) (sorted_evens: List Int) : List Int :=
  let even_indices := (List.range l.length).filter (λ i => i % 2 = 0)
  List.range l.length |>.map (λ i => 
    if i % 2 = 0 then 
      let pos := even_indices.indexOf i
      if pos < sorted_evens.length then sorted_evens.get! pos else l.get! i
    else l.get! i)

def implementation (l: List Int) : List Int := 
  let even_vals := get_even_indexed_elements l
  let sorted_evens := even_vals.mergeSort (fun a b => decide (a ≤ b))
  set_even_indexed_elements l sorted_evens

-- LLM HELPER
lemma set_even_indexed_elements_length (l: List Int) (sorted_evens: List Int) :
  (set_even_indexed_elements l sorted_evens).length = l.length := by
  simp [set_even_indexed_elements]
  rw [List.length_map, List.length_range]

-- LLM HELPER
lemma set_even_indexed_elements_odd_preserved (l: List Int) (sorted_evens: List Int) (i: Nat) :
  i < l.length → i % 2 ≠ 0 → (set_even_indexed_elements l sorted_evens).get! i = l.get! i := by
  intro h_len h_odd
  simp [set_even_indexed_elements]
  have h_in_range : i < (List.range l.length).length := by
    rw [List.length_range]
    exact h_len
  rw [List.get!_map, List.get!_range h_in_range]
  simp [if_neg (Ne.symm (ne_of_not_eq (fun h => h_odd (Eq.symm h))))]

-- LLM HELPER
lemma mergeSort_sorted (l: List Int) : List.Sorted Int.le (l.mergeSort (fun a b => decide (a ≤ b))) := by
  apply List.sorted_mergeSort

-- LLM HELPER
lemma mergeSort_count_eq (l: List Int) (x: Int) : 
  (l.mergeSort (fun a b => decide (a ≤ b))).count x = l.count x := by
  apply List.count_mergeSort

-- LLM HELPER
lemma filter_even_indices_map_get (l: List Int) (sorted_evens: List Int) :
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0)
  let result := set_even_indexed_elements l sorted_evens
  even_idx.length = sorted_evens.length →
  even_idx.map (λ i => result.get! i) = sorted_evens := by
  intro h_len_eq
  simp [set_even_indexed_elements]
  apply List.ext_get
  · simp [List.length_map]
    exact h_len_eq
  · intro n h1 h2
    simp [List.get_map]
    have h_mem : (List.filter (fun i => decide (i % 2 = 0)) (List.range l.length)).get n h1 ∈ List.filter (fun i => decide (i % 2 = 0)) (List.range l.length) := by
      apply List.get_mem
    have h_even : (List.filter (fun i => decide (i % 2 = 0)) (List.range l.length)).get n h1 % 2 = 0 := by
      have h_mem_filter := h_mem
      rw [List.mem_filter] at h_mem_filter
      simp at h_mem_filter
      exact h_mem_filter.2
    simp [h_even]
    have h_pos : List.indexOf (List.get (List.filter (fun i => decide (i % 2 = 0)) (List.range l.length)) n h1) (List.filter (fun i => decide (i % 2 = 0)) (List.range l.length)) < sorted_evens.length := by
      rw [← h_len_eq]
      apply List.indexOf_lt_length.mpr
      exact h_mem
    simp [h_pos]
    have h_idx : List.indexOf (List.get (List.filter (fun i => decide (i % 2 = 0)) (List.range l.length)) n h1) (List.filter (fun i => decide (i % 2 = 0)) (List.range l.length)) = n := by
      apply List.indexOf_get
    rw [h_idx]
    rw [List.get!_eq_get]

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  simp [problem_spec, implementation]
  let even_vals := get_even_indexed_elements l
  let sorted_evens := even_vals.mergeSort (fun a b => decide (a ≤ b))
  let result := set_even_indexed_elements l sorted_evens
  use result
  constructor
  · rfl
  · simp [get_even_indexed_elements]
    constructor
    · exact set_even_indexed_elements_length l sorted_evens
    · constructor
      · intro i h_len h_odd
        exact set_even_indexed_elements_odd_preserved l sorted_evens i h_len h_odd
      · constructor
        · have h_len_eq : ((List.range l.length).filter (λ i => i % 2 = 0)).length = sorted_evens.length := by
            simp [sorted_evens, even_vals, get_even_indexed_elements]
            rw [List.length_mergeSort, List.length_map]
          rw [filter_even_indices_map_get l sorted_evens h_len_eq]
          exact mergeSort_sorted even_vals
        · simp [List.all_eq_true]
          intro x
          have h_count : sorted_evens.count x = even_vals.count x := mergeSort_count_eq even_vals x
          have h_len_eq : ((List.range l.length).filter (λ i => i % 2 = 0)).length = sorted_evens.length := by
            simp [sorted_evens, even_vals, get_even_indexed_elements]
            rw [List.length_mergeSort, List.length_map]
          rw [filter_even_indices_map_get l sorted_evens h_len_eq]
          rw [h_count]
          simp [even_vals, get_even_indexed_elements]