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
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def filterUnique (numbers: List Int) : List Int :=
  List.filter (fun x => numbers.count x = 1) numbers

def implementation (numbers: List Int) : List Int := filterUnique numbers

-- LLM HELPER
lemma mem_filterUnique_iff {numbers : List Int} {x : Int} :
  x ∈ filterUnique numbers ↔ x ∈ numbers ∧ numbers.count x = 1 := by
  unfold filterUnique
  rw [List.mem_filter]

-- LLM HELPER
lemma filterUnique_subset (numbers : List Int) : filterUnique numbers ⊆ numbers := by
  unfold filterUnique
  exact List.filter_subset _ _

-- LLM HELPER
lemma findIndex_exists {numbers : List Int} {x : Int} (h : x ∈ numbers) :
  ∃ i, i < numbers.length ∧ numbers[i]! = x := by
  induction' numbers with head tail ih
  · simp at h
  · simp at h
    cases' h with h h
    · use 0
      simp [h]
    · obtain ⟨i, hi_lt, hi_eq⟩ := ih h
      use i + 1
      simp [hi_lt, hi_eq]

-- LLM HELPER
lemma filter_getElem_in_original {numbers : List Int} {i : Nat} 
  (hi : i < (List.filter (fun x => numbers.count x = 1) numbers).length) :
  (List.filter (fun x => numbers.count x = 1) numbers)[i]! ∈ numbers := by
  have h_mem : (List.filter (fun x => numbers.count x = 1) numbers)[i]! ∈ List.filter (fun x => numbers.count x = 1) numbers :=
    List.getElem_mem _ i hi
  exact List.filter_subset _ _ h_mem

-- LLM HELPER
lemma filter_preserves_order {numbers : List Int} {i j : Nat}
  (hi : i < (List.filter (fun x => numbers.count x = 1) numbers).length)
  (hj : j < (List.filter (fun x => numbers.count x = 1) numbers).length)
  (hij : i < j) :
  ∃ ip jp : Nat, ip < jp ∧ 
  (List.filter (fun x => numbers.count x = 1) numbers)[i]! = numbers[ip]! ∧
  (List.filter (fun x => numbers.count x = 1) numbers)[j]! = numbers[jp]! := by
  let filtered := List.filter (fun x => numbers.count x = 1) numbers
  
  -- Use the fact that filter preserves relative order
  have h_i_in : filtered[i]! ∈ numbers := filter_getElem_in_original hi
  have h_j_in : filtered[j]! ∈ numbers := filter_getElem_in_original hj
  
  -- Find indices in original list
  obtain ⟨ip, hip_lt, hip_eq⟩ := findIndex_exists h_i_in
  obtain ⟨jp, hjp_lt, hjp_eq⟩ := findIndex_exists h_j_in
  
  -- The key insight: we need to find the leftmost occurrences
  -- Since filter preserves order, if i < j in filtered list,
  -- then the first occurrence of filtered[i] comes before first occurrence of filtered[j]
  
  -- Find the actual indices by using List.findIdx
  let idx_i := List.findIdx (fun x => x = filtered[i]!) numbers
  let idx_j := List.findIdx (fun x => x = filtered[j]!) numbers
  
  have h_idx_i_valid : idx_i < numbers.length := by
    rw [List.findIdx_lt_length]
    exact h_i_in
  
  have h_idx_j_valid : idx_j < numbers.length := by
    rw [List.findIdx_lt_length]
    exact h_j_in
  
  have h_idx_i_eq : numbers[idx_i]! = filtered[i]! := by
    exact List.getElem_of_findIdx h_i_in
  
  have h_idx_j_eq : numbers[idx_j]! = filtered[j]! := by
    exact List.getElem_of_findIdx h_j_in
  
  -- The ordering property follows from filter preserving order
  have h_order : idx_i < idx_j := by
    by_contra h_not
    have h_ge : idx_j ≤ idx_i := Nat.le_of_not_gt h_not
    -- This would contradict the filter order preservation
    -- We can prove this by induction on the list structure
    have h_contra : ¬(i < j) := by
      -- If idx_j ≤ idx_i, then filtered[j] appears before or at same position as filtered[i]
      -- But filter preserves order, so this contradicts i < j
      induction' numbers with head tail ih_list generalizing i j
      · simp at hi
      · simp [List.filter] at hi hj
        split_ifs with h_head
        · -- head satisfies condition
          cases' i with i'
          · cases' j with j'
            · simp at hij
            · -- This case leads to contradiction
              simp at h_order hij
              simp [List.findIdx] at h_ge
              split_ifs at h_ge with h_eq_i h_eq_j
              · simp at h_ge
              · simp at h_ge
              · simp at h_ge
                exact Nat.not_lt.mpr h_ge hij
          · -- i = i' + 1, similar analysis
            cases' j with j'
            · simp at hij
            · simp at hij h_ge
              -- Recursive case
              have : ¬(i' < j') := by
                simp [List.findIdx] at h_ge
                split_ifs at h_ge with h_eq_i h_eq_j
                · simp at h_ge
                · simp at h_ge
                · exact Nat.not_lt.mpr (Nat.le_of_succ_le_succ h_ge) hij
              exact this hij
        · -- head doesn't satisfy condition, similar analysis
          simp [List.findIdx] at h_ge
          split_ifs at h_ge with h_eq_i h_eq_j
          · simp at h_ge
          · simp at h_ge
          · exact Nat.not_lt.mpr (Nat.le_of_succ_le_succ h_ge) hij
    exact h_contra hij
  
  use idx_i, idx_j
  exact ⟨h_order, h_idx_i_eq, h_idx_j_eq⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  use filterUnique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      rw [mem_filterUnique_iff] at hi
      exact hi.2
    · constructor
      · intro i hi hcount
        rw [mem_filterUnique_iff]
        exact ⟨hi, hcount⟩
      · intro i j hi hj hij
        unfold filterUnique
        exact filter_preserves_order hi hj hij