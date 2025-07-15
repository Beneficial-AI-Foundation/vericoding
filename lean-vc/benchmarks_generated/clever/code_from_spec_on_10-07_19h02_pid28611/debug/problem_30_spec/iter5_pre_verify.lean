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
lemma count_filter_pos (numbers: List Int) (x: Int) (h: x > 0) : 
  List.count x (numbers.filter (λ y => y > 0)) = List.count x numbers := by
  rw [List.count_filter]
  simp only [decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
  congr 1
  ext y
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · intro hy
    exact hy.2
  · intro hy
    by_cases h_pos : y > 0
    · exact ⟨h_pos, hy⟩
    · simp [h_pos]

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
      rw [List.mem_filter] at hx
      exact ⟨hx.2, hx.1⟩
    · constructor
      · simp [List.all_eq_true]
        intro x hx h_pos
        rw [List.mem_filter]
        exact ⟨hx, h_pos⟩
      · simp [List.all_eq_true]
        intro x hx
        rw [List.mem_filter] at hx
        have h_pos : x > 0 := hx.2
        exact count_filter_pos numbers x h_pos