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
  result.all (λ x => x > 0 ∧ x ∈ numbers) ∧
  numbers.all (λ x => x > 0 → x ∈ result) ∧
  result.all (λ x => result.count x = numbers.count x);
-- program termination
∃ result,
  implementation numbers = result ∧
  spec result

def implementation (numbers: List Int): List Int := numbers.filter (λ x => x > 0)

-- LLM HELPER
lemma filter_pos_all_pos (numbers: List Int) : 
  (numbers.filter (λ x => x > 0)).all (λ x => x > 0) := by
  simp [List.all_filter]

-- LLM HELPER
lemma filter_pos_all_mem (numbers: List Int) : 
  (numbers.filter (λ x => x > 0)).all (λ x => x ∈ numbers) := by
  simp [List.all_filter, List.mem_filter]

-- LLM HELPER
lemma pos_mem_filter (numbers: List Int) : 
  numbers.all (λ x => x > 0 → x ∈ numbers.filter (λ x => x > 0)) := by
  simp [List.all_def, List.mem_filter]

-- LLM HELPER
lemma filter_count_eq (numbers: List Int) : 
  (numbers.filter (λ x => x > 0)).all (λ x => (numbers.filter (λ x => x > 0)).count x = numbers.count x) := by
  simp [List.all_def]
  intro x hx
  rw [List.mem_filter] at hx
  exact List.count_filter_of_pos hx.1

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · constructor
    · exact List.all_and_left.mpr ⟨filter_pos_all_pos numbers, filter_pos_all_mem numbers⟩
    · constructor
      · exact pos_mem_filter numbers
      · exact filter_count_eq numbers