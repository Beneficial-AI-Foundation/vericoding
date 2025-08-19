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
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0);
  let every_third_val_in_result := every_third_idx.map (λ i => result.get! i);
  let every_third_val := every_third_idx.map (λ i => l.get! i);
  (∀ i, i < l.length → (i % 3 ≠ 0 → l.get! i = result.get! i)) ∧
  List.Sorted Int.le every_third_val_in_result ∧
  every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
def extract_every_third (l: List Int) : List Int :=
  (List.range l.length).filter (λ i => i % 3 = 0) |>.map (λ i => l.get! i)

-- LLM HELPER
def set_at_indices (l: List Int) (indices: List Nat) (values: List Int) : List Int :=
  List.range l.length |>.map (λ i => 
    match indices.indexOf? i with
    | some idx => values.get! idx
    | none => l.get! i)

def implementation (l: List Int) : List Int := 
  let every_third_indices := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_values := every_third_indices.map (λ i => l.get! i)
  let sorted_values := every_third_values.mergeSort Int.le
  set_at_indices l every_third_indices sorted_values

-- LLM HELPER
lemma set_at_indices_length (l: List Int) (indices: List Nat) (values: List Int) :
  (set_at_indices l indices values).length = l.length := by
  unfold set_at_indices
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma set_at_indices_preserves_non_indices (l: List Int) (indices: List Nat) (values: List Int) 
  (i: Nat) (h: i < l.length) (h_not_in: i ∉ indices) :
  (set_at_indices l indices values).get! i = l.get! i := by
  unfold set_at_indices
  simp [List.get!_map, List.get!_range, h]
  rw [List.indexOf?_eq_none.mpr h_not_in]
  simp

-- LLM HELPER
lemma set_at_indices_at_indices (l: List Int) (indices: List Nat) (values: List Int) 
  (i: Nat) (h: i < l.length) (h_in: i ∈ indices) (h_idx: indices.indexOf i < values.length) :
  (set_at_indices l indices values).get! i = values.get! (indices.indexOf i) := by
  unfold set_at_indices
  simp [List.get!_map, List.get!_range, h]
  rw [List.indexOf?_eq_some.mpr ⟨h_in, rfl⟩]
  simp

-- LLM HELPER
lemma filter_range_mod_3_sorted (l: List Int) :
  let indices := (List.range l.length).filter (λ i => i % 3 = 0)
  let values := indices.map (λ i => l.get! i)
  let sorted_values := values.mergeSort Int.le
  List.Sorted Int.le sorted_values := by
  simp [List.sorted_mergeSort]

-- LLM HELPER
lemma filter_range_mod_3_count (l: List Int) :
  let indices := (List.range l.length).filter (λ i => i % 3 = 0)
  let values := indices.map (λ i => l.get! i)
  let sorted_values := values.mergeSort Int.le
  values.all (λ x => sorted_values.count x = values.count x) := by
  simp [List.all_eq_true]
  intro x
  exact List.count_mergeSort Int.le values x

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec
  let spec := fun result => 
    l.length = result.length ∧
    let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0);
    let every_third_val_in_result := every_third_idx.map (λ i => result.get! i);
    let every_third_val := every_third_idx.map (λ i => l.get! i);
    (∀ i, i < l.length → (i % 3 ≠ 0 → l.get! i = result.get! i)) ∧
    List.Sorted Int.le every_third_val_in_result ∧
    every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x)
  
  use implementation l
  constructor
  · rfl
  · unfold implementation
    let every_third_indices := (List.range l.length).filter (λ i => i % 3 = 0)
    let every_third_values := every_third_indices.map (λ i => l.get! i)
    let sorted_values := every_third_values.mergeSort Int.le
    let result := set_at_indices l every_third_indices sorted_values
    
    constructor
    · exact set_at_indices_length l every_third_indices sorted_values
    
    constructor
    · intro i hi h_not_mod_3
      have h_not_in : i ∉ every_third_indices := by
        simp [every_third_indices, List.mem_filter, List.mem_range]
        exact h_not_mod_3
      exact set_at_indices_preserves_non_indices l every_third_indices sorted_values i hi h_not_in
    
    constructor
    · simp [every_third_indices, every_third_values, sorted_values]
      exact List.sorted_mergeSort Int.le every_third_values
    
    · simp [every_third_indices, every_third_values, sorted_values]
      exact List.all_eq_true.mp (filter_range_mod_3_count l)