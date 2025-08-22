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
lemma getElem_mem_of_lt (l: List Int) (i: Nat) (h: i < l.length) : l[i] ∈ l := by
  exact List.getElem_mem l i h

-- LLM HELPER
lemma mem_implies_indexOf_lt (l: List Int) (x: Int) (h: x ∈ l) : l.indexOf x < l.length := by
  exact List.indexOf_lt_length.mpr h

-- LLM HELPER
lemma filter_preserves_order (l: List Int) (p: Int → Bool) (i j: Nat) 
  (hi : i < (l.filter p).length) (hj : j < (l.filter p).length) (hij : i < j) :
  l.indexOf (l.filter p)[i] < l.indexOf (l.filter p)[j] := by
  have h1 : (l.filter p)[i] ∈ l := List.mem_of_mem_filter (getElem_mem_of_lt (l.filter p) i hi)
  have h2 : (l.filter p)[j] ∈ l := List.mem_of_mem_filter (getElem_mem_of_lt (l.filter p) j hj)
  have sublist : (l.filter p).Sublist l := List.filter_sublist p l
  exact List.Sublist.indexOf_lt_indexOf sublist (getElem_mem_of_lt (l.filter p) i hi) (getElem_mem_of_lt (l.filter p) j hj) hij

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
          have : filtered[i]! ∈ filtered := by
            simp [List.getElem!_mem]
            exact List.getElem!_mem filtered i
          exact List.mem_of_mem_filter this
        have h2 : filtered[j]! ∈ numbers := by
          have : filtered[j]! ∈ filtered := by
            simp [List.getElem!_mem]
            exact List.getElem!_mem filtered j
          exact List.mem_of_mem_filter this
        
        -- Use indices from original list
        use numbers.indexOf filtered[i]!, numbers.indexOf filtered[j]!
        constructor
        · -- Show ip < jp using sublist property
          exact filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij
        · constructor
          · rfl
          · rfl