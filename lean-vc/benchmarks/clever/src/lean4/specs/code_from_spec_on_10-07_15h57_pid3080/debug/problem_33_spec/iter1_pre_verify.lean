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
def get_indices_mod_3_eq_0 (n : Nat) : List Nat :=
  (List.range n).filter (λ i => i % 3 = 0)

-- LLM HELPER
def extract_elements_at_indices (l : List Int) (indices : List Nat) : List Int :=
  indices.map (λ i => l.get! i)

-- LLM HELPER
def replace_at_indices (l : List Int) (indices : List Nat) (new_vals : List Int) : List Int :=
  List.range l.length |>.map (λ i => 
    match indices.indexOf? i with
    | some idx => new_vals.get! idx
    | none => l.get! i)

def implementation (l: List Int) : List Int := 
  if l.length = 0 then []
  else
    let every_third_idx := get_indices_mod_3_eq_0 l.length
    let every_third_val := extract_elements_at_indices l every_third_idx
    let sorted_every_third := every_third_val.mergeSort
    replace_at_indices l every_third_idx sorted_every_third

-- LLM HELPER
lemma get_indices_mod_3_eq_0_correct (n : Nat) :
  get_indices_mod_3_eq_0 n = (List.range n).filter (λ i => i % 3 = 0) := by
  rfl

-- LLM HELPER
lemma extract_elements_at_indices_correct (l : List Int) (indices : List Nat) :
  extract_elements_at_indices l indices = indices.map (λ i => l.get! i) := by
  rfl

-- LLM HELPER
lemma replace_at_indices_length (l : List Int) (indices : List Nat) (new_vals : List Int) :
  (replace_at_indices l indices new_vals).length = l.length := by
  unfold replace_at_indices
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma replace_at_indices_preserves_non_indices (l : List Int) (indices : List Nat) (new_vals : List Int) (i : Nat) :
  i < l.length → i ∉ indices → (replace_at_indices l indices new_vals).get! i = l.get! i := by
  intro h_len h_not_in
  unfold replace_at_indices
  simp [List.get!_map, List.get!_range]
  rw [List.indexOf?_eq_none.mpr h_not_in]
  simp

-- LLM HELPER
lemma replace_at_indices_updates_indices (l : List Int) (indices : List Nat) (new_vals : List Int) (i : Nat) (j : Nat) :
  i < l.length → j < indices.length → indices.get! j = i → j < new_vals.length →
  (replace_at_indices l indices new_vals).get! i = new_vals.get! j := by
  intro h_len h_j_len h_eq h_new_len
  unfold replace_at_indices
  simp [List.get!_map, List.get!_range]
  have h_indexOf : indices.indexOf? i = some j := by
    rw [← h_eq]
    exact List.indexOf?_get!_of_valid_index h_j_len
  rw [h_indexOf]
  simp

-- LLM HELPER
lemma mergeSort_sorted (l : List Int) : List.Sorted Int.le (l.mergeSort) := by
  exact List.sorted_mergeSort l

-- LLM HELPER
lemma mergeSort_count_eq (l : List Int) (x : Int) : l.mergeSort.count x = l.count x := by
  exact List.count_mergeSort l x

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec
  simp only [implementation]
  split_ifs with h
  · -- case l.length = 0
    simp [h]
    use []
    constructor
    · rfl
    · simp [h]
  · -- case l.length ≠ 0
    let every_third_idx := get_indices_mod_3_eq_0 l.length
    let every_third_val := extract_elements_at_indices l every_third_idx
    let sorted_every_third := every_third_val.mergeSort
    let result := replace_at_indices l every_third_idx sorted_every_third
    
    use result
    constructor
    · rfl
    · constructor
      · exact replace_at_indices_length l every_third_idx sorted_every_third
      · constructor
        · intro i h_len h_not_mod3
          rw [get_indices_mod_3_eq_0_correct]
          have h_not_in : i ∉ (List.range l.length).filter (λ i => i % 3 = 0) := by
            simp [List.mem_filter]
            right
            exact h_not_mod3
          exact replace_at_indices_preserves_non_indices l every_third_idx sorted_every_third i h_len h_not_in
        · constructor
          · rw [get_indices_mod_3_eq_0_correct, extract_elements_at_indices_correct]
            exact mergeSort_sorted every_third_val
          · rw [get_indices_mod_3_eq_0_correct, extract_elements_at_indices_correct]
            intro x
            simp [List.all_iff_forall]
            exact mergeSort_count_eq every_third_val x