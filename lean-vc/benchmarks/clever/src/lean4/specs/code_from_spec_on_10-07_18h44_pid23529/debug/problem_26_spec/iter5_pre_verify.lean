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
lemma findFirstIndex (numbers : List Int) (x : Int) (h : x ∈ numbers) :
  ∃ i, i < numbers.length ∧ numbers[i]! = x ∧ 
  ∀ j, j < i → numbers[j]! ≠ x := by
  induction' numbers with head tail ih generalizing h
  · simp at h
  · simp at h
    cases' h with h h
    · use 0
      simp [h]
    · obtain ⟨i, hi_lt, hi_eq, hi_first⟩ := ih h
      use i + 1
      constructor
      · simp [hi_lt]
      · constructor
        · simp [hi_eq]
        · intro j hj
          cases' j with j'
          · simp
            intro h_eq
            have : head ∈ tail := by
              rw [← h_eq]
              exact h
            have : head ∉ tail := by
              simp [List.mem_cons_iff] at *
              exact fun a => a rfl
            contradiction
          · simp
            exact hi_first j' (Nat.lt_of_succ_lt_succ hj)

-- LLM HELPER
lemma filter_preserves_order (numbers : List Int) :
  ∀ i j : Nat, i < (filterUnique numbers).length → j < (filterUnique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
  (filterUnique numbers)[i]! = numbers[ip]! ∧
  (filterUnique numbers)[j]! = numbers[jp]! := by
  intro i j hi hj hij
  
  let filtered := filterUnique numbers
  
  have h_i_in : filtered[i]! ∈ numbers := by
    have : filtered[i]! ∈ filtered := List.getElem_mem _ i hi
    exact filterUnique_subset numbers this
  
  have h_j_in : filtered[j]! ∈ numbers := by
    have : filtered[j]! ∈ filtered := List.getElem_mem _ j hj
    exact filterUnique_subset numbers this
  
  obtain ⟨ip, hip_lt, hip_eq, hip_first⟩ := findFirstIndex numbers (filtered[i]!) h_i_in
  obtain ⟨jp, hjp_lt, hjp_eq, hjp_first⟩ := findFirstIndex numbers (filtered[j]!) h_j_in
  
  have h_order : ip < jp := by
    by_contra h_not
    have h_ge : jp ≤ ip := Nat.le_of_not_gt h_not
    
    -- This leads to a contradiction with filter preserving order
    have h_contra : ¬(i < j) := by
      -- We prove this by showing that if jp ≤ ip, then the j-th element 
      -- of the filtered list cannot come after the i-th element
      
      -- Key insight: filter preserves the relative order of elements
      -- If jp ≤ ip, then filtered[j] appears before or at same position as filtered[i]
      -- in the original list, which contradicts i < j in the filtered list
      
      induction' numbers with head tail ih_induction
      · simp at hi
      · unfold filterUnique at hi hj
        simp [List.filter] at hi hj
        split_ifs with h_head
        · -- head satisfies the condition
          cases' i with i'
          · -- i = 0
            cases' j with j'
            · simp at hij
            · -- j = j' + 1, i = 0
              simp at hip_eq hjp_eq hip_first hjp_first
              have : jp = 0 := by
                have : numbers[jp]! = head := by
                  rw [← hjp_eq]
                  rfl
                cases' jp with jp'
                · rfl
                · have : numbers[jp'.succ]! = head := this
                  simp at this
                  have : head ∈ tail := by
                    rw [← this]
                    exact List.getElem_mem _ jp' (Nat.lt_of_succ_lt_succ hjp_lt)
                  have : head ∉ tail := by
                    intro h_in
                    simp [List.mem_cons_iff] at h_in
                    exact hjp_first 0 (Nat.zero_lt_succ jp') rfl
                  contradiction
              have : ip = 0 := by
                rw [← hip_eq]
                simp
                cases' ip with ip'
                · rfl
                · have : numbers[ip'.succ]! = head := by
                    rw [hip_eq]
                    rfl
                  simp at this
                  have : head ∈ tail := by
                    rw [← this]
                    exact List.getElem_mem _ ip' (Nat.lt_of_succ_lt_succ hip_lt)
                  have : head ∉ tail := by
                    intro h_in
                    simp [List.mem_cons_iff] at h_in
                    exact hip_first 0 (Nat.zero_lt_succ ip') rfl
                  contradiction
              rw [this] at h_ge
              rw [this] at h_ge
              simp at h_ge
              exact Nat.not_lt_zero j' (Nat.lt_of_succ_lt_succ hij)
          · -- i = i' + 1
            cases' j with j'
            · simp at hij
            · -- Both i and j are successors
              simp at hip_eq hjp_eq
              have : i' < j' := Nat.lt_of_succ_lt_succ hij
              -- Apply induction hypothesis to tail
              have : ¬(i' < j') := by
                -- This follows from the induction hypothesis
                exact this
              exact this this
        · -- head doesn't satisfy the condition
          have : i < (List.filter (fun x => tail.count x = 1) tail).length := by
            simp [List.filter] at hi
            exact hi
          have : j < (List.filter (fun x => tail.count x = 1) tail).length := by
            simp [List.filter] at hj
            exact hj
          -- Apply induction hypothesis
          exact hij
    
    exact h_contra hij
  
  use ip, jp
  exact ⟨h_order, hip_eq, hjp_eq⟩

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
      · exact filter_preserves_order numbers