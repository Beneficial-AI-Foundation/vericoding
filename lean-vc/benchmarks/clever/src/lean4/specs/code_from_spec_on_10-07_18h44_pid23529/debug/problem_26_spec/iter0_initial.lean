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
lemma filterUnique_preserves_order {numbers : List Int} {i j : Nat} :
  i < (filterUnique numbers).length → j < (filterUnique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filterUnique numbers)[i]! = numbers[ip]! ∧ (filterUnique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  unfold filterUnique
  have h_sub := List.filter_subset (fun x => numbers.count x = 1) numbers
  have h_i : (List.filter (fun x => numbers.count x = 1) numbers)[i]! ∈ numbers := by
    have : (List.filter (fun x => numbers.count x = 1) numbers)[i]! ∈ List.filter (fun x => numbers.count x = 1) numbers := by
      apply List.getElem_mem
      exact hi
    exact h_sub this
  have h_j : (List.filter (fun x => numbers.count x = 1) numbers)[j]! ∈ numbers := by
    have : (List.filter (fun x => numbers.count x = 1) numbers)[j]! ∈ List.filter (fun x => numbers.count x = 1) numbers := by
      apply List.getElem_mem
      exact hj
    exact h_sub this
  have h_indices := List.filter_indices_exist_ordered (fun x => numbers.count x = 1) numbers i j hi hj hij
  obtain ⟨ip, jp, hip, hjp, h_lt, h_eq_i, h_eq_j⟩ := h_indices
  use ip, jp
  exact ⟨h_lt, h_eq_i, h_eq_j⟩

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
      · exact filterUnique_preserves_order