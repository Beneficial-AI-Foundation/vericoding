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
lemma filter_positive_mem {numbers : List Int} {x : Int} (h : x ∈ numbers.filter (λ y => y > 0)) : x ∈ numbers := by
  exact List.mem_of_mem_filter h

-- LLM HELPER
lemma filter_positive_prop {numbers : List Int} {x : Int} (h : x ∈ numbers.filter (λ y => y > 0)) : x > 0 := by
  exact List.of_mem_filter h

-- LLM HELPER
lemma mem_filter_of_mem_and_prop {numbers : List Int} {x : Int} (h_mem : x ∈ numbers) (h_prop : x > 0) : x ∈ numbers.filter (λ y => y > 0) := by
  exact List.mem_filter.mpr ⟨h_mem, h_prop⟩

-- LLM HELPER
lemma count_filter_eq {numbers : List Int} {x : Int} (h : x > 0) : (numbers.filter (λ y => y > 0)).count x = numbers.count x := by
  simp [List.count_filter]
  split_ifs with h'
  · rfl
  · contradiction

-- LLM HELPER
lemma count_filter_zero {numbers : List Int} {x : Int} (h : ¬x > 0) : (numbers.filter (λ y => y > 0)).count x = 0 := by
  simp [List.count_filter]
  split_ifs with h'
  · contradiction
  · rfl

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · simp [List.all_eq_true]
    constructor
    · intro x h
      constructor
      · exact filter_positive_prop h
      · exact filter_positive_mem h
    · constructor
      · intro x h_mem h_pos
        exact mem_filter_of_mem_and_prop h_mem h_pos
      · intro x h_mem
        by_cases h : x > 0
        · exact count_filter_eq h
        · rw [count_filter_zero h]
          simp [List.count_eq_zero]
          intro h_mem_orig
          exact h (filter_positive_prop (mem_filter_of_mem_and_prop h_mem_orig h))