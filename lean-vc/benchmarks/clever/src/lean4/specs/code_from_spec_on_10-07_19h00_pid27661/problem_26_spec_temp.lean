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
  unfold filter_unique
  simp [List.mem_filter]

-- LLM HELPER
lemma filter_unique_count_eq_one (numbers: List Int) (x: Int) :
  x ∈ filter_unique numbers → numbers.count x = 1 := by
  intro h
  rw [mem_filter_unique_iff] at h
  exact h.2

-- LLM HELPER
lemma filter_unique_preserves_order (numbers: List Int) :
  ∀ i j : Nat, i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro i j hi hj hij
  unfold filter_unique
  have h1 : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers := by
    have : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers.filter (fun x => numbers.count x = 1) := by
      apply List.getElem!_mem
      exact hi
    rw [List.mem_filter] at this
    exact this.1
  have h2 : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers := by
    have : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers.filter (fun x => numbers.count x = 1) := by
      apply List.getElem!_mem
      exact hj
    rw [List.mem_filter] at this
    exact this.1
  obtain ⟨ip, hip, heq1⟩ := List.mem_iff_get.mp h1
  obtain ⟨jp, hjp, heq2⟩ := List.mem_iff_get.mp h2
  have order_preserved : ip < jp := by
    have filtered_sublist : numbers.filter (fun x => numbers.count x = 1) <+ numbers := List.filter_sublist
    have get_i : (numbers.filter (fun x => numbers.count x = 1)).get ⟨i, hi⟩ = numbers.get ⟨ip, hip⟩ := by
      rw [← heq1]
      simp [List.get_eq_getElem]
    have get_j : (numbers.filter (fun x => numbers.count x = 1)).get ⟨j, hj⟩ = numbers.get ⟨jp, hjp⟩ := by
      rw [← heq2]
      simp [List.get_eq_getElem]
    exact List.Sublist.getElem_lt_getElem_of_lt filtered_sublist hij get_i get_j
  use ip, jp
  constructor
  · exact order_preserved
  constructor
  · simp [List.getElem!_eq_getElem]
    exact heq1.symm
  · simp [List.getElem!_eq_getElem]
    exact heq2.symm

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use filter_unique numbers
  constructor
  · rfl
  constructor
  · intro i hi
    exact filter_unique_count_eq_one numbers i hi
  constructor
  · intro i hi hcount
    rw [mem_filter_unique_iff]
    exact ⟨hi, hcount⟩
  · exact filter_unique_preserves_order numbers