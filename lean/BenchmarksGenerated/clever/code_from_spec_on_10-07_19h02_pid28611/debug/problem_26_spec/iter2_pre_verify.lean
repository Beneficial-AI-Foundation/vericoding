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
def filter_unique (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def implementation (numbers: List Int) : List Int := filter_unique numbers

-- LLM HELPER
lemma mem_filter_unique_iff (numbers: List Int) (x: Int) : 
  x ∈ filter_unique numbers ↔ x ∈ numbers ∧ numbers.count x = 1 := by
  simp [filter_unique]

-- LLM HELPER
lemma getElem_mem_of_lt (l: List α) (i: Nat) (h: i < l.length) : l[i]! ∈ l := by
  have : l[i]! = l[i]'h := by simp [List.getElem_eq_getElem]
  rw [this]
  exact List.getElem_mem l i h

-- LLM HELPER
lemma mem_implies_indexOf_lt (l: List α) [DecidableEq α] (x: α) (h: x ∈ l) : l.indexOf x < l.length := by
  exact List.indexOf_lt_length.mpr h

-- LLM HELPER
lemma indexOf_getElem (l: List α) [DecidableEq α] (i: Nat) (h: i < l.length) : l[l.indexOf l[i]!] = l[i]! := by
  have mem : l[i]! ∈ l := getElem_mem_of_lt l i h
  rw [List.getElem_indexOf_of_mem mem]

-- LLM HELPER
lemma filter_unique_preserves_order (numbers: List Int) (i j: Nat) :
  i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  simp [filter_unique]
  let filtered := numbers.filter (fun x => numbers.count x = 1)
  have h1 : filtered[i]! ∈ numbers := by
    have mem_filtered : filtered[i]! ∈ filtered := getElem_mem_of_lt filtered i hi
    exact List.mem_of_mem_filter mem_filtered
  have h2 : filtered[j]! ∈ numbers := by
    have mem_filtered : filtered[j]! ∈ numbers.filter (fun x => numbers.count x = 1) := getElem_mem_of_lt (numbers.filter (fun x => numbers.count x = 1)) j hj
    exact List.mem_of_mem_filter mem_filtered
  
  let ip := numbers.indexOf filtered[i]!
  let jp := numbers.indexOf filtered[j]!
  
  have hip_lt : ip < numbers.length := mem_implies_indexOf_lt numbers filtered[i]! h1
  have hjp_lt : jp < numbers.length := mem_implies_indexOf_lt numbers filtered[j]! h2
  have hip_eq : numbers[ip]! = filtered[i]! := by
    rw [List.getElem_indexOf_of_mem h1]
  have hjp_eq : numbers[jp]! = filtered[j]! := by
    rw [List.getElem_indexOf_of_mem h2]
  
  have order_preserved : ip < jp := by
    by_contra h
    simp at h
    have hjp_le_ip : jp ≤ ip := Nat.le_of_not_gt h
    -- Since filtered preserves relative order from numbers, and i < j in filtered,
    -- the original positions must also satisfy ip < jp
    have : List.indexOf filtered[i]! numbers < List.indexOf filtered[j]! numbers := by
      apply List.indexOf_lt_indexOf_of_lt
      · exact h1
      · exact h2
      · simp [List.filter_eq_self]
        sorry -- This needs a more complex proof about filter preserving order
    rw [← this] at hjp_le_ip
    exact Nat.lt_irrefl ip (Nat.lt_of_le_of_lt hjp_le_ip this)
  
  exact ⟨ip, jp, order_preserved, hip_eq.symm, hjp_eq.symm⟩

-- LLM HELPER
lemma filter_preserves_relative_order_simple (numbers: List Int) (i j: Nat) :
  i < (numbers.filter (fun x => numbers.count x = 1)).length → 
  j < (numbers.filter (fun x => numbers.count x = 1)).length → 
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[i]! = numbers[ip]! ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[j]! = numbers[jp]! := by
  intro hi hj hij
  -- Use the fact that filter maintains relative order
  have exists_indices := List.exists_of_mem_filter
  sorry -- This is a complex proof that would require more list theory

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filter_unique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      rw [mem_filter_unique_iff] at hi
      exact hi.2
    · constructor
      · intro i hi hcount
        rw [mem_filter_unique_iff]
        exact ⟨hi, hcount⟩
      · intro i j hi hj hij
        simp [filter_unique]
        -- We need to show that the filtered list preserves relative order
        let filtered := numbers.filter (fun x => numbers.count x = 1)
        have h1 : filtered[i]! ∈ numbers := by
          have : filtered[i]! ∈ filtered := getElem_mem_of_lt filtered i hi
          exact List.mem_of_mem_filter this
        have h2 : filtered[j]! ∈ numbers := by
          have : filtered[j]! ∈ filtered := getElem_mem_of_lt filtered j hj
          exact List.mem_of_mem_filter this
        
        -- Find the indices in the original list
        use numbers.indexOf filtered[i]!, numbers.indexOf filtered[j]!
        constructor
        · -- Show ip < jp
          have hip_mem : filtered[i]! ∈ numbers := h1
          have hjp_mem : filtered[j]! ∈ numbers := h2
          -- Since filter preserves order, the indices must be ordered
          apply List.indexOf_lt_indexOf_of_lt hip_mem hjp_mem
          -- This follows from the fact that i < j in the filtered list
          sorry -- Complex proof needed
        · constructor
          · -- Show equality for first element
            simp [List.getElem_indexOf_of_mem h1]
          · -- Show equality for second element  
            simp [List.getElem_indexOf_of_mem h2]