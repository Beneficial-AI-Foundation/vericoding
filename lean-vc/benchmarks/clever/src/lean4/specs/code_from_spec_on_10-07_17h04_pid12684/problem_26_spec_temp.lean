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
  numbers.filter (fun x => numbers.count x = 1)

def implementation (numbers: List Int) : List Int := filterUnique numbers

-- LLM HELPER
lemma filter_mem_iff (numbers: List Int) (x: Int) : 
  x ∈ filterUnique numbers ↔ x ∈ numbers ∧ numbers.count x = 1 := by
  unfold filterUnique
  simp [List.mem_filter]

-- LLM HELPER
lemma filter_preserves_order (numbers: List Int) (i j: Nat) :
  i < (filterUnique numbers).length → j < (filterUnique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ ip < numbers.length ∧ jp < numbers.length ∧ 
  (filterUnique numbers)[i]! = numbers[ip]! ∧ (filterUnique numbers)[j]! = numbers[jp]! := by
  unfold filterUnique
  intro hi hj hij
  have h1 : ∃ ip, ip < numbers.length ∧ (numbers.filter (fun x => numbers.count x = 1))[i]! = numbers[ip]! := by
    apply List.getElem_filter_exists
    exact hi
  have h2 : ∃ jp, jp < numbers.length ∧ (numbers.filter (fun x => numbers.count x = 1))[j]! = numbers[jp]! := by
    apply List.getElem_filter_exists
    exact hj
  obtain ⟨ip, hip_lt, hip_eq⟩ := h1
  obtain ⟨jp, hjp_lt, hjp_eq⟩ := h2
  have order : ip < jp := by
    apply List.filter_preserves_relative_order
    · exact hip_lt
    · exact hjp_lt
    · exact hij
    · exact hip_eq.symm
    · exact hjp_eq.symm
  use ip, jp
  exact ⟨order, hip_lt, hjp_lt, hip_eq, hjp_eq⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use filterUnique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      have := filter_mem_iff numbers i
      rw [this] at hi
      exact hi.2
    · constructor
      · intro i hi hcount
        have := filter_mem_iff numbers i
        rw [this]
        exact ⟨hi, hcount⟩
      · intro i j hi hj hij
        have := filter_preserves_order numbers i j hi hj hij
        obtain ⟨ip, jp, hip_lt, _, _, hip_eq, hjp_eq⟩ := this
        use ip, jp
        exact ⟨hip_lt, hip_eq, hjp_eq⟩