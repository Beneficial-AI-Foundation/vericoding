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
lemma filter_unique_subset (numbers: List Int) : 
  ∀ x, x ∈ filter_unique numbers → x ∈ numbers := by
  intro x h
  rw [mem_filter_unique_iff] at h
  exact h.1

-- LLM HELPER
lemma filter_unique_count_one (numbers: List Int) : 
  ∀ x, x ∈ filter_unique numbers → numbers.count x = 1 := by
  intro x h
  rw [mem_filter_unique_iff] at h
  exact h.2

-- LLM HELPER
lemma filter_unique_complete (numbers: List Int) : 
  ∀ x, x ∈ numbers → numbers.count x = 1 → x ∈ filter_unique numbers := by
  intro x h_mem h_count
  rw [mem_filter_unique_iff]
  exact ⟨h_mem, h_count⟩

-- LLM HELPER
lemma filter_preserves_order (numbers: List Int) : 
  ∀ i j : Nat, i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro i j hi hj hij
  simp [filter_unique] at hi hj
  have h1 : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers := by
    apply filter_unique_subset
    simp [filter_unique]
    apply List.getElem!_mem
    exact hi
  have h2 : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers := by
    apply filter_unique_subset
    simp [filter_unique]
    apply List.getElem!_mem
    exact hj
  obtain ⟨ip, hip, heq1⟩ := List.mem_iff_get.mp h1
  obtain ⟨jp, hjp, heq2⟩ := List.mem_iff_get.mp h2
  have : ip < jp := by
    apply List.filter_preserves_order
    · exact hij
    · simp [filter_unique] at hi hj
      convert hi
    · simp [filter_unique] at hi hj
      convert hj
    · rw [← heq1, List.getElem!_eq_get]
      simp [filter_unique]
    · rw [← heq2, List.getElem!_eq_get]
      simp [filter_unique]
  use ip, jp
  constructor
  · exact this
  constructor
  · rw [← heq1, List.getElem!_eq_get]
    simp [filter_unique]
  · rw [← heq2, List.getElem!_eq_get]
    simp [filter_unique]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filter_unique numbers
  constructor
  · rfl
  constructor
  · intro i hi
    exact filter_unique_count_one numbers i hi
  constructor
  · intro i h_mem h_count
    exact filter_unique_complete numbers i h_mem h_count
  · exact filter_preserves_order numbers