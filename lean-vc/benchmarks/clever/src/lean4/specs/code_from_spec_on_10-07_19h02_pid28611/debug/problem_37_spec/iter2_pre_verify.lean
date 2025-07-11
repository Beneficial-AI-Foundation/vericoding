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
  let sorted_evens := even_vals.mergeSort (fun a b => a ≤ b)
  set_even_indexed_elements l sorted_evens

-- LLM HELPER
lemma get_even_indexed_elements_correct (l: List Int) :
  get_even_indexed_elements l = ((List.range l.length).filter (λ i => i % 2 = 0)).map (λ i => l.get! i) := by
  rfl

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
  rw [List.get!_map]
  simp [h_odd]

-- LLM HELPER
lemma mergeSort_sorted (l: List Int) : List.Sorted Int.le (l.mergeSort (fun a b => a ≤ b)) := by
  apply List.sorted_mergeSort

-- LLM HELPER
lemma mergeSort_count_eq (l: List Int) (x: Int) : 
  (l.mergeSort (fun a b => a ≤ b)).count x = l.count x := by
  apply List.count_mergeSort

-- LLM HELPER
lemma filter_even_indices_map_get (l: List Int) (sorted_evens: List Int) :
  let even_idx := (List.range l.length).filter (λ i => i % 2 = 0)
  let result := set_even_indexed_elements l sorted_evens
  even_idx.length = sorted_evens.length →
  even_idx.map (λ i => result.get! i) = sorted_evens := by
  intro h_len_eq
  simp [set_even_indexed_elements]
  have h_map : even_idx.map (λ i => (List.range l.length |>.map (λ j => 
    if j % 2 = 0 then 
      let pos := even_idx.indexOf j
      if pos < sorted_evens.length then sorted_evens.get! pos else l.get! j
    else l.get! j)).get! i) = even_idx.map (λ i => sorted_evens.get! (even_idx.indexOf i)) := by
    congr 1
    funext i
    simp
    have h_even : i % 2 = 0 := by
      simp [even_idx] at *
      exact List.of_mem_filter _ _
    rw [List.get!_map]
    simp [h_even]
    have h_pos : even_idx.indexOf i < sorted_evens.length := by
      rw [← h_len_eq]
      apply List.indexOf_lt_length.mpr
      simp [even_idx]
      exact List.mem_filter.mp ⟨List.mem_range.mpr h_len_eq, h_even⟩
    simp [h_pos]
  rw [h_map]
  have h_bij : even_idx.map (λ i => sorted_evens.get! (even_idx.indexOf i)) = sorted_evens := by
    apply List.ext_get
    · rw [List.length_map, h_len_eq]
    · intro n h1 h2
      simp [List.get_map]
      have h_nth : even_idx.get! n = even_idx.get! (even_idx.indexOf (even_idx.get! n)) := by
        simp [List.get!_indexOf]
      rw [← h_nth]
      simp [List.indexOf_get]
  exact h_bij

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  simp [problem_spec, implementation]
  let even_vals := get_even_indexed_elements l
  let sorted_evens := even_vals.mergeSort (fun a b => a ≤ b)
  let result := set_even_indexed_elements l sorted_evens
  use result
  constructor
  · rfl
  · simp [get_even_indexed_elements_correct]
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
          rw [h_count]
          simp [even_vals, get_even_indexed_elements]
          have h_len_eq : ((List.range l.length).filter (λ i => i % 2 = 0)).length = sorted_evens.length := by
            simp [sorted_evens, even_vals, get_even_indexed_elements]
            rw [List.length_mergeSort, List.length_map]
          rw [filter_even_indices_map_get l sorted_evens h_len_eq]
          exact mergeSort_count_eq even_vals x