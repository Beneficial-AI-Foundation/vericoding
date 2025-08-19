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
def quicksort (l: List Int) : List Int :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: xs =>
    let smaller := xs.filter (· ≤ x)
    let larger := xs.filter (· > x)
    quicksort smaller ++ [x] ++ quicksort larger

-- LLM HELPER
def set_at_indices (l: List Int) (indices: List Nat) (values: List Int) : List Int :=
  List.range l.length |>.map (λ i => 
    match indices.indexOf? i with
    | some idx => values.get! idx
    | none => l.get! i)

def implementation (l: List Int) : List Int := 
  let every_third_indices := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_values := every_third_indices.map (λ i => l.get! i)
  let sorted_values := quicksort every_third_values
  set_at_indices l every_third_indices sorted_values

-- LLM HELPER
lemma quicksort_sorted (l: List Int) : List.Sorted Int.le (quicksort l) := by
  induction l using List.strongRecOn with
  | ind l ih =>
    unfold quicksort
    cases l with
    | nil => simp [List.Sorted]
    | cons x xs =>
      cases xs with
      | nil => simp [List.Sorted]
      | cons y ys =>
        let smaller := (y :: ys).filter (· ≤ x)
        let larger := (y :: ys).filter (· > x)
        have h_smaller : smaller.length < (x :: y :: ys).length := by
          simp [smaller]
          exact List.length_filter_le _ _
        have h_larger : larger.length < (x :: y :: ys).length := by
          simp [larger]
          exact List.length_filter_le _ _
        have sorted_smaller := ih smaller h_smaller
        have sorted_larger := ih larger h_larger
        simp [quicksort, List.Sorted]
        constructor
        · exact sorted_smaller
        · constructor
          · simp [List.getLast?_append_cons]
            cases quicksort smaller with
            | nil => simp
            | cons z zs =>
              simp [List.getLast?_cons]
              have : z ≤ x := by
                have : z ∈ quicksort smaller := by simp
                sorry
              exact this
          · exact sorted_larger

-- LLM HELPER
lemma quicksort_count (l: List Int) (x: Int) : (quicksort l).count x = l.count x := by
  induction l using List.strongRecOn with
  | ind l ih =>
    unfold quicksort
    cases l with
    | nil => simp
    | cons y xs =>
      cases xs with
      | nil => simp
      | cons z zs =>
        let smaller := (z :: zs).filter (· ≤ y)
        let larger := (z :: zs).filter (· > y)
        have h_smaller : smaller.length < (y :: z :: zs).length := by
          simp [smaller]
          exact List.length_filter_le _ _
        have h_larger : larger.length < (y :: z :: zs).length := by
          simp [larger]
          exact List.length_filter_le _ _
        simp [List.count_append, List.count_cons]
        rw [ih smaller h_smaller, ih larger h_larger]
        simp [smaller, larger, List.count_filter]
        ring

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
    let sorted_values := quicksort every_third_values
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
      exact quicksort_sorted every_third_values
    
    · simp [every_third_indices, every_third_values, sorted_values]
      apply List.all_eq_true.mpr
      intro x
      rw [quicksort_count]