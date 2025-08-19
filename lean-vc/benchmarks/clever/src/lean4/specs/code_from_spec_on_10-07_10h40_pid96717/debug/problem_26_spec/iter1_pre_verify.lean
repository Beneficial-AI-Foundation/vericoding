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
  intros i j hi hj hij
  have h1 : (filter_unique numbers)[i]! ∈ numbers := by
    rw [mem_filter_unique_iff]
    constructor
    · have : (filter_unique numbers)[i]! ∈ filter_unique numbers := by
        apply List.getElem_mem
        exact hi
      rw [mem_filter_unique_iff] at this
      exact this.1
    · have : (filter_unique numbers)[i]! ∈ filter_unique numbers := by
        apply List.getElem_mem
        exact hi
      rw [mem_filter_unique_iff] at this
      exact this.2
  have h2 : (filter_unique numbers)[j]! ∈ numbers := by
    rw [mem_filter_unique_iff]
    constructor
    · have : (filter_unique numbers)[j]! ∈ filter_unique numbers := by
        apply List.getElem_mem
        exact hj
      rw [mem_filter_unique_iff] at this
      exact this.1
    · have : (filter_unique numbers)[j]! ∈ filter_unique numbers := by
        apply List.getElem_mem
        exact hj
      rw [mem_filter_unique_iff] at this
      exact this.2
  obtain ⟨ip, hip, heq1⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨jp, hjp, heq2⟩ := List.mem_iff_getElem.mp h2
  have order_preserved : ip < jp := by
    by_contra h
    push_neg at h
    have : jp ≤ ip := Nat.le_of_not_gt h
    have : jp < ip ∨ jp = ip := Nat.lt_or_eq_of_le this
    cases this with
    | inl hjp_lt_hip =>
      have : j < i := by
        apply List.filter_lt_of_lt
        exact hjp_lt_hip
        rw [heq2, heq1]
        simp [filter_unique]
      linarith
    | inr hjp_eq_hip =>
      rw [hjp_eq_hip] at heq2
      rw [heq1] at heq2
      have : (filter_unique numbers)[i]! = (filter_unique numbers)[j]! := heq2
      have : i = j := by
        apply List.getElem_inj
        exact this
      linarith
  exact ⟨ip, jp, order_preserved, heq1, heq2⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
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