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
lemma count_filter_eq (numbers: List Int) (x: Int) : 
  List.count x (numbers.filter (λ y => y > 0)) = 
  if x > 0 then List.count x numbers else 0 := by
  rw [List.count_filter]
  simp only [decide_eq_true_iff]
  split_ifs with h
  · simp [h]
  · simp [h]

-- LLM HELPER
lemma mem_filter_iff (numbers: List Int) (x: Int) :
  x ∈ numbers.filter (λ y => y > 0) ↔ x > 0 ∧ x ∈ numbers := by
  exact List.mem_filter

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · constructor
    · simp [List.all_eq_true]
      intro x hx
      rw [mem_filter_iff] at hx
      exact hx
    · constructor
      · simp [List.all_eq_true]
        intro x hx h_pos
        rw [mem_filter_iff]
        exact ⟨h_pos, hx⟩
      · simp [List.all_eq_true]
        intro x hx
        rw [mem_filter_iff] at hx
        have h_pos : x > 0 := hx.1
        rw [count_filter_eq]
        simp [h_pos]