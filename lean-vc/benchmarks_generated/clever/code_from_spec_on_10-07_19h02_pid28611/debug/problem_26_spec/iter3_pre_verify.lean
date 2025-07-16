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
  simp [filter_unique, List.mem_filter]

-- LLM HELPER
lemma getElem_mem_of_lt (l: List α) (i: Nat) (h: i < l.length) : l[i]! ∈ l := by
  exact List.getElem_mem l i

-- LLM HELPER
lemma mem_implies_indexOf_lt (l: List α) [DecidableEq α] (x: α) (h: x ∈ l) : l.indexOf x < l.length := by
  exact List.indexOf_lt_length.mpr h

-- LLM HELPER
lemma indexOf_getElem (l: List α) [DecidableEq α] (i: Nat) (h: i < l.length) : l[l.indexOf l[i]!] = l[i]! := by
  have mem : l[i]! ∈ l := getElem_mem_of_lt l i h
  rw [List.get_indexOf_of_mem mem]

-- LLM HELPER
lemma filter_maintains_order (numbers: List Int) (i j: Nat) :
  i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  simp [filter_unique]
  let filtered := numbers.filter (fun x => numbers.count x = 1)
  
  -- Elements in filtered list are in original list
  have h1 : filtered[i]! ∈ numbers := by
    have mem_filtered : filtered[i]! ∈ filtered := getElem_mem_of_lt filtered i hi
    exact List.mem_of_mem_filter mem_filtered
  have h2 : filtered[j]! ∈ numbers := by
    have mem_filtered : filtered[j]! ∈ filtered := getElem_mem_of_lt filtered j hj
    exact List.mem_of_mem_filter mem_filtered
  
  -- Get indices in original list
  let ip := numbers.indexOf filtered[i]!
  let jp := numbers.indexOf filtered[j]!
  
  have hip_lt : ip < numbers.length := mem_implies_indexOf_lt numbers filtered[i]! h1
  have hjp_lt : jp < numbers.length := mem_implies_indexOf_lt numbers filtered[j]! h2
  
  -- The key insight: filter maintains relative order
  have order_preserved : ip < jp := by
    -- Use the fact that filtered[i] appears before filtered[j] in the original list
    -- since filtering preserves order
    have sub_ij : filtered.take (j + 1) = filtered.take i ++ [filtered[i]!] ++ (filtered.drop (i + 1)).take (j - i) := by
      simp [List.take_add_drop]
    have : List.indexOf filtered[i]! numbers < List.indexOf filtered[j]! numbers := by
      apply List.indexOf_lt_indexOf_of_lt h1 h2
      -- This follows from the sublist property of filter
      have : filtered.IsSublist numbers := List.filter_sublist _ _
      -- The relative order is preserved in sublists
      exact List.IsSublist.indexOf_le_indexOf this (by assumption) (by assumption) hij
    exact this
  
  exact ⟨ip, jp, order_preserved, (List.get_indexOf_of_mem h1).symm, (List.get_indexOf_of_mem h2).symm⟩

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
        let filtered := numbers.filter (fun x => numbers.count x = 1)
        
        -- Get elements and their membership in original list
        have h1 : filtered[i]! ∈ numbers := by
          have : filtered[i]! ∈ filtered := getElem_mem_of_lt filtered i hi
          exact List.mem_of_mem_filter this
        have h2 : filtered[j]! ∈ numbers := by
          have : filtered[j]! ∈ filtered := getElem_mem_of_lt filtered j hj
          exact List.mem_of_mem_filter this
        
        -- Use indices from original list
        use numbers.indexOf filtered[i]!, numbers.indexOf filtered[j]!
        constructor
        · -- Show ip < jp using sublist property
          apply List.indexOf_lt_indexOf_of_lt h1 h2
          -- Filter preserves relative order
          have : filtered.IsSublist numbers := List.filter_sublist _ _
          exact List.IsSublist.indexOf_le_indexOf this (by assumption) (by assumption) hij
        · constructor
          · exact (List.get_indexOf_of_mem h1).symm
          · exact (List.get_indexOf_of_mem h2).symm