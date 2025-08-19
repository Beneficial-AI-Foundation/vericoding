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
lemma filter_unique_preserves_order (numbers: List Int) :
  ∀ i j : Nat, i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro i j hi hj hij
  simp [filter_unique] at hi hj
  have h1 : (numbers.filter (fun x => numbers.count x = 1))[i]! ∈ numbers := by
    apply List.mem_of_getElem_mem
    rw [List.getElem_filter]
    simp
  have h2 : (numbers.filter (fun x => numbers.count x = 1))[j]! ∈ numbers := by
    apply List.mem_of_getElem_mem
    rw [List.getElem_filter]
    simp
  obtain ⟨ip, hip, heq1⟩ := List.getElem_of_mem h1
  obtain ⟨jp, hjp, heq2⟩ := List.getElem_of_mem h2
  use ip, jp
  constructor
  · have : i < j := hij
    have filter_preserves_order : ∀ (l : List Int) (p : Int → Bool) (i j : Nat), 
      i < (l.filter p).length → j < (l.filter p).length → i < j →
      ∃ ip jp : Nat, ip < jp ∧ ip < l.length ∧ jp < l.length ∧
      (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
      intro l p i' j' hi' hj' hij'
      sorry -- This is a complex lemma about filter preserving order
    obtain ⟨ip', jp', hip_jp, _, _, heq1', heq2'⟩ := filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij
    exact hip_jp
  constructor
  · rw [filter_unique]
    rw [List.getElem_filter]
    exact heq1
  · rw [filter_unique]
    rw [List.getElem_filter]
    exact heq2

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filter_unique numbers
  constructor
  · rfl
  · simp [filter_unique]
    constructor
    · intro i hi
      rw [mem_filter_unique_iff] at hi
      exact hi.2
    constructor
    · intro i hi hcount
      rw [mem_filter_unique_iff]
      exact ⟨hi, hcount⟩
    · exact filter_unique_preserves_order numbers