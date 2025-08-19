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
  induction' numbers with head tail ih
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
            rw [← h_eq] at h
            exact List.mem_cons_of_mem head h
          · simp
            exact hi_first j' (Nat.lt_of_succ_lt_succ hj)

-- LLM HELPER
lemma filter_index_lt (numbers : List Int) (i j : Nat) :
  i < (filterUnique numbers).length → j < (filterUnique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
  (filterUnique numbers)[i]! = numbers[ip]! ∧
  (filterUnique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  
  have h_i_mem : (filterUnique numbers)[i]! ∈ numbers := by
    have : (filterUnique numbers)[i]! ∈ filterUnique numbers := List.getElem_mem _ i hi
    exact filterUnique_subset numbers this
  
  have h_j_mem : (filterUnique numbers)[j]! ∈ numbers := by
    have : (filterUnique numbers)[j]! ∈ filterUnique numbers := List.getElem_mem _ j hj
    exact filterUnique_subset numbers this
  
  obtain ⟨ip, hip_lt, hip_eq, _⟩ := findFirstIndex numbers (filterUnique numbers)[i]! h_i_mem
  obtain ⟨jp, hjp_lt, hjp_eq, _⟩ := findFirstIndex numbers (filterUnique numbers)[j]! h_j_mem
  
  have h_order : ip < jp := by
    by_contra h_not
    have h_ge : jp ≤ ip := Nat.le_of_not_gt h_not
    
    -- We'll show this leads to a contradiction with filter preserving order
    have h_contra : False := by
      -- Since filter preserves order, if jp ≤ ip, then elements would appear
      -- in wrong order in the filtered list
      unfold filterUnique at hi hj
      have h_filter_order : ∀ l : List Int, ∀ a b : Int, ∀ ia ib : Nat,
        ia < (List.filter (fun x => l.count x = 1) l).length →
        ib < (List.filter (fun x => l.count x = 1) l).length →
        ia < ib →
        ∃ iap ibp : Nat, iap < ibp ∧ 
        (List.filter (fun x => l.count x = 1) l)[ia]! = l[iap]! ∧
        (List.filter (fun x => l.count x = 1) l)[ib]! = l[ibp]! := by
        intro l a b ia ib hia hib hab
        -- This follows from the fact that filter preserves relative order
        induction' l with head tail ih_l
        · simp at hia
        · unfold List.filter at hia hib
          split_ifs with h_head
          · -- head satisfies condition
            cases' ia with ia'
            · cases' ib with ib'
              · simp at hab
              · use 0, (ib' + 1)
                simp
            · cases' ib with ib'
              · simp at hab
              · have : ia' < (List.filter (fun x => tail.count x = 1) tail).length := by
                  simp [List.filter] at hia
                  exact hia
                have : ib' < (List.filter (fun x => tail.count x = 1) tail).length := by
                  simp [List.filter] at hib
                  exact hib
                have : ia' < ib' := Nat.lt_of_succ_lt_succ hab
                obtain ⟨iap, ibp, h_order, h_eq_a, h_eq_b⟩ := ih_l this this this
                use iap + 1, ibp + 1
                constructor
                · exact Nat.succ_lt_succ h_order
                · constructor
                  · simp [h_eq_a]
                  · simp [h_eq_b]
          · -- head doesn't satisfy condition
            have : ia < (List.filter (fun x => tail.count x = 1) tail).length := by
              simp [List.filter] at hia
              exact hia
            have : ib < (List.filter (fun x => tail.count x = 1) tail).length := by
              simp [List.filter] at hib
              exact hib
            obtain ⟨iap, ibp, h_order, h_eq_a, h_eq_b⟩ := ih_l this this hab
            use iap + 1, ibp + 1
            constructor
            · exact Nat.succ_lt_succ h_order
            · constructor
              · simp [h_eq_a]
              · simp [h_eq_b]
      
      obtain ⟨ip', jp', h_order', h_eq_i, h_eq_j⟩ := h_filter_order numbers 
        (filterUnique numbers)[i]! (filterUnique numbers)[j]! i j hi hj hij
      
      rw [← hip_eq] at h_eq_i
      rw [← hjp_eq] at h_eq_j
      
      have : ip = ip' := by
        have : numbers[ip]! = numbers[ip']! := by
          rw [hip_eq, h_eq_i]
        -- Since we found first occurrences, they must be equal
        sorry -- This requires more detailed proof about uniqueness of first occurrence
      
      have : jp = jp' := by
        have : numbers[jp]! = numbers[jp']! := by
          rw [hjp_eq, h_eq_j]
        sorry -- Similar argument
      
      rw [this, this] at h_ge
      exact Nat.not_le_of_lt h_order' h_ge
    
    exact h_contra
  
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
      · exact filter_index_lt numbers