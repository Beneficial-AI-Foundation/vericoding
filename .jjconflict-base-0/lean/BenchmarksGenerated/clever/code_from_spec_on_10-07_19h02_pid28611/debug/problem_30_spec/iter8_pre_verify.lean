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
lemma mem_filter_iff (numbers: List Int) (x: Int) :
  x ∈ numbers.filter (λ y => y > 0) ↔ x > 0 ∧ x ∈ numbers := by
  rw [List.mem_filter]
  simp only [decide_eq_true_iff]

-- LLM HELPER
lemma count_filter_pos (numbers: List Int) (x: Int) (hx_pos: x > 0) :
  List.count x (numbers.filter (λ y => y > 0)) = List.count x numbers := by
  rw [List.count_filter]
  simp only [decide_eq_true_iff]
  congr
  ext y
  simp only [Bool.and_iff_left_iff_imp]
  intro h_eq
  rw [h_eq]
  exact hx_pos

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
        exact count_filter_pos numbers x h_pos