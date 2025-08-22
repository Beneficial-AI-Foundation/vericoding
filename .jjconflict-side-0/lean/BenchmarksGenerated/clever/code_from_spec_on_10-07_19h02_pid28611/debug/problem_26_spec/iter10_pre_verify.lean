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
lemma filter_preserves_order (l: List Int) (p: Int → Bool) (i j: Nat) 
  (hi : i < (l.filter p).length) (hj : j < (l.filter p).length) (hij : i < j) :
  l.indexOf (l.filter p)[i]'(by omega) < l.indexOf (l.filter p)[j]'(by omega) := by
  have h1 : (l.filter p)[i]'(by omega) ∈ l := List.mem_of_mem_filter (List.get_mem (l.filter p) i)
  have h2 : (l.filter p)[j]'(by omega) ∈ l := List.mem_of_mem_filter (List.get_mem (l.filter p) j)
  have sublist : (l.filter p).Sublist l := List.filter_sublist p l
  exact List.Sublist.indexOf_lt_indexOf sublist (List.get_mem (l.filter p) i) (List.get_mem (l.filter p) j) hij

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
          have elem_mem : filtered[i]! ∈ filtered := by
            apply List.getElem!_mem
            omega
          exact List.mem_of_mem_filter elem_mem
        have h2 : filtered[j]! ∈ numbers := by
          have elem_mem : filtered[j]! ∈ filtered := by
            apply List.getElem!_mem
            omega
          exact List.mem_of_mem_filter elem_mem
        
        -- Use indices from original list
        use numbers.indexOf filtered[i]!, numbers.indexOf filtered[j]!
        constructor
        · -- Show ip < jp using sublist property
          exact filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij
        · constructor
          · simp [List.getElem!_pos]
            have idx_lt : numbers.indexOf filtered[i]! < numbers.length := List.indexOf_lt_length.mpr h1
            rw [List.getElem!_pos numbers (numbers.indexOf filtered[i]!) idx_lt]
            exact List.getElem_indexOf h1
          · simp [List.getElem!_pos]
            have idx_lt : numbers.indexOf filtered[j]! < numbers.length := List.indexOf_lt_length.mpr h2
            rw [List.getElem!_pos numbers (numbers.indexOf filtered[j]!) idx_lt]
            exact List.getElem_indexOf h2