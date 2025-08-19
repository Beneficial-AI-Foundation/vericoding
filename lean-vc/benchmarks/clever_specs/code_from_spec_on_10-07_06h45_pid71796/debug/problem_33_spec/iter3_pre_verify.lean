def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  l.length = result.length ∧
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0);
  let every_third_val_in_result := every_third_idx.map (λ i => result[i]!);
  let every_third_val := every_third_idx.map (λ i => l[i]!);
  (∀ i, i < l.length → (i % 3 ≠ 0 → l[i]! = result[i]!)) ∧
  List.Sorted (· ≤ ·) every_third_val_in_result ∧
  every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x);
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
def extract_every_third (l: List Int) : List Int :=
  let indices := List.range l.length |>.filter (λ i => i % 3 = 0)
  indices.map (λ i => l[i]!)

-- LLM HELPER
def sort_every_third_positions (l: List Int) : List Int :=
  let indices := List.range l.length |>.filter (λ i => i % 3 = 0)
  let values := indices.map (λ i => l[i]!)
  let sorted_values := values.toArray.qsort |>.toList
  
  let rec replace_at_indices (original: List Int) (idx_list: List Nat) (val_list: List Int) : List Int :=
    match original with
    | [] => []
    | h :: t =>
      if idx_list.contains 0 then
        match val_list with
        | [] => h :: replace_at_indices t (idx_list.map (λ x => x - 1)) []
        | v :: vs => v :: replace_at_indices t (idx_list.map (λ x => x - 1)) vs
      else
        h :: replace_at_indices t (idx_list.map (λ x => x - 1)) val_list
  
  replace_at_indices l indices sorted_values

def implementation (l: List Int) : List Int := 
  let indices := List.range l.length |>.filter (λ i => i % 3 = 0)
  let values := indices.map (λ i => l[i]!)
  let sorted_values := values.toArray.qsort |>.toList
  
  let rec build_result (i: Nat) (sorted_vals: List Int) : List Int :=
    if i >= l.length then []
    else if i % 3 = 0 then
      match sorted_vals with
      | [] => (l[i]!) :: build_result (i + 1) []
      | v :: vs => v :: build_result (i + 1) vs
    else
      (l[i]!) :: build_result (i + 1) sorted_vals
  
  build_result 0 sorted_values

-- LLM HELPER
lemma build_result_length (l: List Int) (i: Nat) (sorted_vals: List Int) :
  (build_result l i sorted_vals).length = if i >= l.length then 0 else l.length - i := by
  induction' l.length - i using Nat.strong_induction_on with n ih
  simp [build_result]
  if h : i >= l.length then
    simp [h]
  else
    simp [h]
    if h' : i % 3 = 0 then
      simp [h']
      cases sorted_vals with
      | nil => simp; rw [ih]; simp; omega
      | cons v vs => simp; rw [ih]; simp; omega
    else
      simp [h']
      rw [ih]
      simp
      omega

-- LLM HELPER  
lemma implementation_length (l: List Int) : (implementation l).length = l.length := by
  unfold implementation
  convert build_result_length l 0 _
  simp

-- LLM HELPER
lemma implementation_preserves_non_third (l: List Int) (i: Nat) :
  i < l.length → i % 3 ≠ 0 → (implementation l)[i]! = l[i]! := by
  intros h_lt h_not_third
  unfold implementation
  sorry

-- LLM HELPER
lemma implementation_sorts_third_positions (l: List Int) :
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val_in_result := every_third_idx.map (λ i => (implementation l)[i]!)
  List.Sorted (· ≤ ·) every_third_val_in_result := by
  sorry

-- LLM HELPER
lemma implementation_preserves_counts (l: List Int) :
  let every_third_idx := (List.range l.length).filter (λ i => i % 3 = 0)
  let every_third_val_in_result := every_third_idx.map (λ i => (implementation l)[i]!)
  let every_third_val := every_third_idx.map (λ i => l[i]!)
  every_third_val.all (λ x => every_third_val_in_result.count x = every_third_val.count x) := by
  sorry

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  use implementation l
  constructor
  · rfl
  · constructor
    · exact implementation_length l
    · constructor
      · intros i hi h_not_third
        exact implementation_preserves_non_third l i hi h_not_third
      · constructor
        · exact implementation_sorts_third_positions l
        · exact implementation_preserves_counts l