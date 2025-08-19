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
def findIndexInOriginal (numbers : List Int) (x : Int) : Option Nat :=
  List.findIdx (fun y => y = x) numbers

-- LLM HELPER
lemma findIndexInOriginal_spec {numbers : List Int} {x : Int} :
  x ∈ numbers → ∃ i, findIndexInOriginal numbers x = some i ∧ i < numbers.length ∧ numbers[i]! = x := by
  intro h
  unfold findIndexInOriginal
  have idx := List.findIdx_of_mem h
  use List.findIdx (fun y => y = x) numbers
  constructor
  · rfl
  · constructor
    · exact List.findIdx_lt_length_of_exists ⟨x, h, rfl⟩
    · rw [List.getElem_findIdx]
      exact rfl

-- LLM HELPER
lemma filterUnique_preserves_order {numbers : List Int} {i j : Nat} :
  i < (filterUnique numbers).length → j < (filterUnique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filterUnique numbers)[i]! = numbers[ip]! ∧ (filterUnique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  unfold filterUnique
  let filtered := List.filter (fun x => numbers.count x = 1) numbers
  have h_sub := List.filter_subset (fun x => numbers.count x = 1) numbers
  have h_i_mem : filtered[i]! ∈ numbers := by
    have : filtered[i]! ∈ filtered := List.getElem_mem filtered i hi
    exact h_sub this
  have h_j_mem : filtered[j]! ∈ numbers := by
    have : filtered[j]! ∈ filtered := List.getElem_mem filtered j hj
    exact h_sub this
  
  -- Find indices in original list
  obtain ⟨ip, hip_some, hip_lt, hip_eq⟩ := findIndexInOriginal_spec h_i_mem
  obtain ⟨jp, hjp_some, hjp_lt, hjp_eq⟩ := findIndexInOriginal_spec h_j_mem
  
  -- We need to show ip < jp
  have h_order : ip < jp := by
    by_contra h_not_lt
    have h_ge : jp ≤ ip := Nat.le_of_not_gt h_not_lt
    -- Since filter preserves order, if i < j in filtered list, 
    -- then the corresponding indices in original list satisfy ip < jp
    have h_filter_order := List.filter_preserves_order (fun x => numbers.count x = 1) numbers i j hi hj hij
    exact Nat.lt_irrefl ip (Nat.lt_of_le_of_lt h_ge h_filter_order)
  
  use ip, jp
  exact ⟨h_order, hip_eq.symm, hjp_eq.symm⟩

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