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
def get_every_third_values (l: List Int) : List Int :=
  let indices := (List.range l.length).filter (λ i => i % 3 = 0)
  indices.map (λ i => l.get! i)

-- LLM HELPER
def replace_at_indices (l: List Int) (indices: List Nat) (values: List Int) : List Int :=
  List.range l.length |>.map (λ i =>
    match indices.indexOf i with
    | Option.none => l.get! i
    | Option.some j => values.get! j
  )

-- LLM HELPER
def int_le_decidable (a b : Int) : Bool := a ≤ b

def implementation (l: List Int) : List Int :=
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val := get_every_third_values l
  let sorted_every_third_val := every_third_val.mergeSort int_le_decidable
  replace_at_indices l every_third_idx sorted_every_third_val

-- LLM HELPER
lemma length_preserved (l: List Int) : 
  (implementation l).length = l.length := by
  simp [implementation, replace_at_indices]
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma non_third_unchanged (l: List Int) (i: Nat) (hi: i < l.length) (hmod: i % 3 ≠ 0) :
  (implementation l).get! i = l.get! i := by
  simp [implementation, replace_at_indices]
  simp [List.get!_map]
  have h_not_mem : i ∉ (List.range l.length).filter (λ j => j % 3 = 0) := by
    intro h_mem
    simp [List.mem_filter, List.mem_range] at h_mem
    exact hmod h_mem.2
  rw [List.indexOf_eq_none.mpr h_not_mem]
  simp

-- LLM HELPER
lemma every_third_sorted (l: List Int) :
  let result := implementation l
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val_in_result := every_third_idx.map (λ i => result.get! i)
  List.Sorted Int.le every_third_val_in_result := by
  simp [implementation, replace_at_indices]
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val := get_every_third_values l
  let sorted_vals := every_third_val.mergeSort int_le_decidable
  have h_sorted : List.Sorted Int.le sorted_vals := by
    apply List.sorted_mergeSort
    intro a b
    simp [int_le_decidable]
  
  have h_map_eq : every_third_idx.map (λ i => 
    (List.range l.length).map (λ j => 
      match every_third_idx.indexOf j with
      | Option.none => l.get! j
      | Option.some k => sorted_vals.get! k
    ).get! i) = sorted_vals := by
    ext n
    simp [List.get_map]
    have h_mem : every_third_idx[n]! ∈ every_third_idx := by
      apply List.get!_mem
      simp [List.length_pos_iff_exists_mem]
      use every_third_idx[n]!
      apply List.get!_mem
    have h_idx : every_third_idx.indexOf (every_third_idx[n]!) = some n := by
      apply List.indexOf_get!
    rw [h_idx]
    simp
  
  rw [h_map_eq]
  exact h_sorted

-- LLM HELPER
lemma count_preserved (l: List Int) :
  let result := implementation l
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val_in_result := every_third_idx.map (λ i => result.get! i)
  let every_third_val := every_third_idx.map (λ i => l.get! i)
  every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x) := by
  simp [implementation, replace_at_indices, get_every_third_values]
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val := every_third_idx.map (λ i => l.get! i)
  let sorted_vals := every_third_val.mergeSort int_le_decidable
  
  have h_perm : every_third_val ~ sorted_vals := List.perm_mergeSort _
  have h_count_eq : ∀ x, every_third_val.count x = sorted_vals.count x := 
    λ x => List.Perm.count_eq h_perm x
  
  have h_map_eq : every_third_idx.map (λ i => 
    (List.range l.length).map (λ j => 
      match every_third_idx.indexOf j with
      | Option.none => l.get! j
      | Option.some k => sorted_vals.get! k
    ).get! i) = sorted_vals := by
    ext n
    simp [List.get_map]
    have h_mem : every_third_idx[n]! ∈ every_third_idx := by
      apply List.get!_mem
      simp [List.length_pos_iff_exists_mem]
      use every_third_idx[n]!
      apply List.get!_mem
    have h_idx : every_third_idx.indexOf (every_third_idx[n]!) = some n := by
      apply List.indexOf_get!
    rw [h_idx]
    simp
  
  rw [h_map_eq]
  apply List.all_of_forall
  intro x
  rw [h_count_eq]

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  use implementation l
  constructor
  · rfl
  · constructor
    · rw [length_preserved l]
    · constructor
      · intro i hi hmod
        rw [non_third_unchanged l i hi hmod]
      · constructor
        · exact every_third_sorted l
        · exact count_preserved l