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
  simp [List.all_iff_forall, List.mem_filter]

-- LLM HELPER
lemma filter_pos_all_mem (numbers: List Int) : 
  (numbers.filter (λ x => x > 0)).all (λ x => x ∈ numbers) := by
  simp [List.all_iff_forall, List.mem_filter]

-- LLM HELPER
lemma pos_mem_filter (numbers: List Int) : 
  numbers.all (λ x => x > 0 → x ∈ numbers.filter (λ x => x > 0)) := by
  simp [List.all_iff_forall, List.mem_filter]

-- LLM HELPER
lemma filter_count_eq (numbers: List Int) : 
  (numbers.filter (λ x => x > 0)).all (λ x => (numbers.filter (λ x => x > 0)).count x = numbers.count x) := by
  simp [List.all_iff_forall]
  intro x hx
  rw [List.mem_filter] at hx
  rw [List.count_filter]
  congr 1
  ext y
  simp [decide_eq_true_iff]
  constructor
  · intro h
    cases' h with h_pos h_eq
    rw [h_eq]
    exact h_pos
  · intro h
    constructor
    · exact h
    · rfl

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · constructor
    · simp [List.all_iff_forall]
      intro x hx
      rw [List.mem_filter] at hx
      exact ⟨hx.1, hx.2⟩
    · constructor
      · exact pos_mem_filter numbers
      · exact filter_count_eq numbers