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
lemma filter_unique_preserves_order (numbers: List Int) (i j: Nat) :
  i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  simp [filter_unique]
  have h1 : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers := by
    apply List.mem_of_mem_filter
    apply List.getElem_mem
  have h2 : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers := by
    apply List.mem_of_mem_filter
    apply List.getElem_mem
  obtain ⟨ip, hip_lt, hip_eq⟩ := List.getElem_of_mem h1
  obtain ⟨jp, hjp_lt, hjp_eq⟩ := List.getElem_of_mem h2
  have order_preserved : ip < jp := by
    by_contra h
    simp at h
    have hjp_le_ip : jp ≤ ip := Nat.le_of_not_gt h
    have filter_order := List.filter_preserves_relative_order (fun x => numbers.count x = 1) numbers i j hij
    rw [hip_eq, hjp_eq] at filter_order
    have : jp < ip := filter_order hjp_le_ip
    exact Nat.lt_irrefl ip (Nat.lt_trans this (Nat.le_refl ip))
  exact ⟨ip, jp, order_preserved, hip_eq.symm, hjp_eq.symm⟩

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
      · exact filter_unique_preserves_order numbers