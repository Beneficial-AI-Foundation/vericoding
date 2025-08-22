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
    match indices.indexOf? i with
    | some idx => if idx < new_vals.length then new_vals[idx]?.getD 0 else l[i]?.getD 0
    | none => l[i]?.getD 0
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
  have h_not_found : indices.indexOf? i = none := by
    rw [List.indexOf?_eq_none]
    exact hni
  simp [h_not_found]

-- LLM HELPER
theorem update_at_indices_updates_indices (l: List Int) (indices: List Nat) (new_vals: List Int) :
  ∀ i idx, i < l.length → indices.indexOf? i = some idx → idx < new_vals.length →
  (update_at_indices l indices new_vals)[i]! = new_vals[idx]! := by
  intro i idx hi hidx hlen
  unfold update_at_indices
  simp [List.getElem!_map]
  have h_range : (List.range l.length)[i]? = some i := by
    rw [List.getElem?_range]
    exact hi
  simp [h_range, hidx, hlen]

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
  (List.range n)[i]'(List.length_range n ▸ h) = i := by
  exact List.getElem_range i h

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
    
    have h_eq : every_third_indices.map (fun i => result[i]!) = sorted_values := by
      apply List.ext_get
      · simp [List.length_map]
        unfold sorted_values get_every_third_values
        simp [List.length_mergeSort, List.length_map]
      · intro n h1 h2
        simp [List.get_map]
        have h_nth : every_third_indices[n] < l.length := by
          have h_mem : every_third_indices[n] ∈ every_third_indices := List.getElem_mem
          simp [List.mem_filter, List.mem_range] at h_mem
          exact h_mem.1
        have hidx : every_third_indices.indexOf? (every_third_indices[n]) = some n := by
          apply List.indexOf?_getElem
          exact h1
        have hlen : n < sorted_values.length := by
          rw [List.length_mergeSort]
          unfold get_every_third_values
          simp [List.length_map]
          exact h1
        exact update_at_indices_updates_indices l every_third_indices sorted_values (every_third_indices[n]) n h_nth hidx hlen
    
    rw [h_eq]
    exact h_sorted
  
  · unfold get_every_third_indices
    simp only [List.map_map, List.all_eq_true]
    intro x
    have h_eq : every_third_indices.map (fun i => result[i]!) = sorted_values := by
      apply List.ext_get
      · simp [List.length_map]
        unfold sorted_values get_every_third_values
        simp [List.length_mergeSort, List.length_map]
      · intro n h1 h2
        simp [List.get_map]
        have h_nth : every_third_indices[n] < l.length := by
          have h_mem : every_third_indices[n] ∈ every_third_indices := List.getElem_mem
          simp [List.mem_filter, List.mem_range] at h_mem
          exact h_mem.1
        have hidx : every_third_indices.indexOf? (every_third_indices[n]) = some n := by
          apply List.indexOf?_getElem
          exact h1
        have hlen : n < sorted_values.length := by
          rw [List.length_mergeSort]
          unfold get_every_third_values
          simp [List.length_map]
          exact h1
        exact update_at_indices_updates_indices l every_third_indices sorted_values (every_third_indices[n]) n h_nth hidx hlen
    
    rw [h_eq]
    unfold sorted_values
    exact mergeSort_count_eq every_third_values x