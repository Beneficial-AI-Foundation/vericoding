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
def update_at_indices (l: List Int) (indices: List Nat) (new_vals: List Int) : List Int :=
  List.range l.length |>.map (λ i => 
    match indices.findIdx (· = i) with
    | n => if n < new_vals.length ∧ n < indices.length ∧ indices[n]? = some i then 
             new_vals[n]?.getD (l[i]?.getD 0) 
           else l[i]?.getD 0
  )

-- LLM HELPER
def get_every_third_values (l: List Int) : List Int :=
  (List.range l.length).filter (λ i => i % 3 = 0) |>.map (λ i => l[i]!)

-- LLM HELPER
def get_every_third_indices (l: List Int) : List Nat :=
  (List.range l.length).filter (λ i => i % 3 = 0)

def implementation (l: List Int) : List Int :=
  let every_third_indices := get_every_third_indices l
  let every_third_values := get_every_third_values l
  let sorted_values := every_third_values.mergeSort (fun x y => x ≤ y)
  update_at_indices l every_third_indices sorted_values

-- LLM HELPER
theorem update_at_indices_length (l: List Int) (indices: List Nat) (new_vals: List Int) :
  (update_at_indices l indices new_vals).length = l.length := by
  unfold update_at_indices
  simp [List.length_map, List.length_range]

-- LLM HELPER
theorem update_at_indices_preserves_non_indices (l: List Int) (indices: List Nat) (new_vals: List Int) :
  ∀ i, i < l.length → i ∉ indices → (update_at_indices l indices new_vals)[i]! = l[i]! := by
  intro i hi hni
  unfold update_at_indices
  simp [List.getElem!_map]
  have h_range : (List.range l.length)[i]? = some i := by
    rw [List.getElem?_range]
    exact hi
  simp [h_range]
  have h_not_found : indices.findIdx (· = i) = indices.length := by
    rw [List.findIdx_eq_length]
    exact hni
  simp [h_not_found]
  have : indices.length < new_vals.length ∨ ¬(indices.length < new_vals.length) := by
    exact Classical.em _
  cases this with
  | inl h => 
    simp [h]
    have : indices.length < indices.length := by
      rw [h_not_found] at *
      exact Nat.lt_irrefl _
    simp [this]
  | inr h =>
    simp [h]

-- LLM HELPER
theorem get_every_third_indices_filter (l: List Int) :
  get_every_third_indices l = (List.range l.length).filter (λ i => i % 3 = 0) := by
  rfl

-- LLM HELPER
theorem get_every_third_values_map (l: List Int) :
  get_every_third_values l = (get_every_third_indices l).map (λ i => l[i]!) := by
  unfold get_every_third_values get_every_third_indices
  rfl

-- LLM HELPER
theorem mergeSort_sorted (l : List Int) :
  List.Sorted (· ≤ ·) (l.mergeSort (fun x y => x ≤ y)) := by
  apply List.sorted_mergeSort
  intro a b c hab hbc
  exact le_trans hab hbc

-- LLM HELPER
theorem mergeSort_count_eq (l : List Int) (x : Int) :
  (l.mergeSort (fun x y => x ≤ y)).count x = l.count x := by
  apply List.count_mergeSort

-- LLM HELPER
theorem range_get (n : Nat) (i : Nat) (h : i < n) : 
  (List.range n)[i] = i := by
  have : i < (List.range n).length := by
    rw [List.length_range]
    exact h
  exact List.getElem_range i this

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  unfold problem_spec implementation
  let every_third_indices := get_every_third_indices l
  let every_third_values := get_every_third_values l
  let sorted_values := every_third_values.mergeSort (fun x y => x ≤ y)
  let result := update_at_indices l every_third_indices sorted_values
  
  use result
  constructor
  · rfl
  
  constructor
  · exact update_at_indices_length l every_third_indices sorted_values
  
  constructor
  · intro i hi hmod
    have hni : i ∉ every_third_indices := by
      unfold get_every_third_indices
      simp [List.mem_filter, List.mem_range]
      exact fun _ => hmod
    exact update_at_indices_preserves_non_indices l every_third_indices sorted_values i hi hni
  
  constructor
  · unfold get_every_third_indices
    simp only [List.map_map]
    have h_sorted : List.Sorted (· ≤ ·) sorted_values := mergeSort_sorted every_third_values
    
    -- We need to show that mapping the indices gives us the sorted values
    have h_eq : every_third_indices.map (fun i => result[i]!) = sorted_values := by
      sorry
    
    rw [h_eq]
    exact h_sorted
  
  · unfold get_every_third_indices
    simp only [List.map_map, List.all_eq_true]
    intro x
    
    -- We need to show count equality
    have h_eq : every_third_indices.map (fun i => result[i]!) = sorted_values := by
      sorry
    
    rw [h_eq]
    unfold sorted_values
    rw [mergeSort_count_eq]
    rfl