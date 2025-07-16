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
  simp [List.getElem!_map']
  have h_range : i < (List.range l.length).length := by
    rw [List.length_range]
    exact hi
  have h_range_eq : (List.range l.length)[i] = i := by
    rw [List.getElem_range _ _ h_range]
  simp [h_range_eq]
  have h_not_found : indices.findIdx (· = i) = indices.length := by
    rw [List.findIdx_eq_length]
    intro x hx
    simp
    have : x ≠ i := by
      intro h
      rw [h] at hx
      exact hni hx
    exact this
  simp [h_not_found]
  have : indices.length < new_vals.length ∨ ¬(indices.length < new_vals.length) := by
    exact Classical.em _
  cases this with
  | inl h => 
    simp [h]
    have : ¬(indices.length < indices.length) := by
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

-- LLM HELPER
theorem update_at_indices_get_at_index (l: List Int) (indices: List Nat) (new_vals: List Int) (i : Nat) (hi : i < l.length) :
  i ∈ indices → 
  (∃ j, j < indices.length ∧ indices[j] = i ∧ j < new_vals.length) →
  (update_at_indices l indices new_vals)[i]! = new_vals[indices.findIdx (· = i)]! := by
  intro h_mem h_ex
  obtain ⟨j, hj_lt, hj_eq, hj_lt_vals⟩ := h_ex
  unfold update_at_indices
  simp [List.getElem!_map']
  have h_range : i < (List.range l.length).length := by
    rw [List.length_range]
    exact hi
  have h_range_eq : (List.range l.length)[i] = i := by
    rw [List.getElem_range _ _ h_range]
  simp [h_range_eq]
  have h_found : indices.findIdx (· = i) < indices.length := by
    rw [List.findIdx_lt_length]
    exact h_mem
  have h_found_eq : indices[indices.findIdx (· = i)] = i := by
    exact List.getElem_findIdx h_mem
  simp [h_found, h_found_eq]
  have : indices.findIdx (· = i) < new_vals.length := by
    have : indices.findIdx (· = i) ≤ j := by
      apply List.findIdx_le_of_mem
      exact h_mem
      exact hj_eq
    exact Nat.lt_of_le_of_lt this hj_lt_vals
  simp [this]

-- LLM HELPER
theorem get_every_third_indices_distinct (l: List Int) :
  (get_every_third_indices l).Nodup := by
  unfold get_every_third_indices
  apply List.Nodup.filter
  exact List.nodup_range _

-- LLM HELPER
theorem get_every_third_values_length (l: List Int) :
  (get_every_third_values l).length = (get_every_third_indices l).length := by
  unfold get_every_third_values get_every_third_indices
  simp [List.length_map]

-- LLM HELPER
theorem update_at_indices_maps_correctly (l: List Int) (indices: List Nat) (new_vals: List Int) :
  indices.length = new_vals.length →
  indices.Nodup →
  (∀ i, i ∈ indices → i < l.length) →
  indices.map (fun i => (update_at_indices l indices new_vals)[i]!) = new_vals := by
  intro hlen hnodup hvalid
  ext j
  simp [List.getElem_map]
  have hj_bound : j < indices.length := by
    apply List.getElem_mem_length
  have hj_mem : indices[j] ∈ indices := List.getElem_mem _ _ _
  have hj_lt : indices[j] < l.length := hvalid _ hj_mem
  have hex : ∃ k, k < indices.length ∧ indices[k] = indices[j] ∧ k < new_vals.length := by
    use j
    constructor
    · exact hj_bound
    constructor
    · rfl
    · rw [←hlen]
      exact hj_bound
  have heq := update_at_indices_get_at_index l indices new_vals (indices[j]) hj_lt hj_mem hex
  rw [heq]
  have hfind : indices.findIdx (· = indices[j]) = j := by
    apply List.findIdx_getElem hnodup
  rw [hfind]

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
      intro _
      exact hmod
    exact update_at_indices_preserves_non_indices l every_third_indices sorted_values i hi hni
  
  constructor
  · have h_sorted : List.Sorted (· ≤ ·) sorted_values := mergeSort_sorted every_third_values
    
    have h_eq : every_third_indices.map (fun i => result[i]!) = sorted_values := by
      unfold result sorted_values every_third_values every_third_indices
      apply update_at_indices_maps_correctly
      · exact get_every_third_values_length l
      · exact get_every_third_indices_distinct l
      · intro i hi
        unfold get_every_third_indices at hi
        simp [List.mem_filter, List.mem_range] at hi
        exact hi.1
    
    rw [h_eq]
    exact h_sorted
  
  · simp only [List.all_eq_true]
    intro x
    
    have h_eq : every_third_indices.map (fun i => result[i]!) = sorted_values := by
      unfold result sorted_values every_third_values every_third_indices
      apply update_at_indices_maps_correctly
      · exact get_every_third_values_length l
      · exact get_every_third_indices_distinct l
      · intro i hi
        unfold get_every_third_indices at hi
        simp [List.mem_filter, List.mem_range] at hi
        exact hi.1
    
    rw [h_eq]
    unfold sorted_values
    rw [mergeSort_count_eq]
    rfl