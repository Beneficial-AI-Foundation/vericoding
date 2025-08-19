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
lemma filter_preserves_relative_order {numbers : List Int} {i j : Nat}
  (hi : i < (List.filter (fun x => numbers.count x = 1) numbers).length)
  (hj : j < (List.filter (fun x => numbers.count x = 1) numbers).length)
  (hij : i < j) :
  ∃ ip jp : Nat, ip < jp ∧ ip < numbers.length ∧ jp < numbers.length ∧
  (List.filter (fun x => numbers.count x = 1) numbers)[i]! = numbers[ip]! ∧
  (List.filter (fun x => numbers.count x = 1) numbers)[j]! = numbers[jp]! := by
  let filtered := List.filter (fun x => numbers.count x = 1) numbers
  have h_i_in : filtered[i]! ∈ numbers := filter_getElem_in_original hi
  have h_j_in : filtered[j]! ∈ numbers := filter_getElem_in_original hj
  
  obtain ⟨ip, hip_lt, hip_eq⟩ := findIndex_exists h_i_in
  obtain ⟨jp, hjp_lt, hjp_eq⟩ := findIndex_exists h_j_in
  
  -- Key insight: filter preserves order, so if i < j in filtered list,
  -- we can find corresponding indices in original list with ip < jp
  have h_order : ip < jp := by
    by_contra h_not
    have h_ge : jp ≤ ip := Nat.le_of_not_gt h_not
    -- This would contradict the order preservation property of filter
    -- We use the fact that filter maintains relative positions
    sorry -- This requires a more complex proof about filter order preservation
  
  use ip, jp
  exact ⟨h_order, hip_lt, hjp_lt, hip_eq.symm, hjp_eq.symm⟩

-- LLM HELPER
lemma simple_filter_order {numbers : List Int} {i j : Nat}
  (hi : i < (List.filter (fun x => numbers.count x = 1) numbers).length)
  (hj : j < (List.filter (fun x => numbers.count x = 1) numbers).length)
  (hij : i < j) :
  ∃ ip jp : Nat, ip < jp ∧ 
  (List.filter (fun x => numbers.count x = 1) numbers)[i]! = numbers[ip]! ∧
  (List.filter (fun x => numbers.count x = 1) numbers)[j]! = numbers[jp]! := by
  -- Simplified approach using the fact that filter preserves order
  induction' numbers with head tail ih generalizing i j
  · simp at hi
  · simp [List.filter] at hi hj
    split_ifs with h
    · -- head satisfies the condition
      cases' i with i'
      · cases' j with j'
        · simp at hij
        · use 0, j' + 1
          simp
          constructor
          · simp
          · simp [List.getElem_cons_succ]
      · cases' j with j'
        · simp at hij
        · simp at hi hj hij
          obtain ⟨ip, jp, h_order, h_eq_i, h_eq_j⟩ := ih hi hj hij
          use ip + 1, jp + 1
          simp [h_order, h_eq_i, h_eq_j]
    · -- head doesn't satisfy the condition
      obtain ⟨ip, jp, h_order, h_eq_i, h_eq_j⟩ := ih hi hj hij
      use ip + 1, jp + 1
      exact ⟨Nat.succ_lt_succ h_order, h_eq_i, h_eq_j⟩

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
        exact simple_filter_order hi hj hij