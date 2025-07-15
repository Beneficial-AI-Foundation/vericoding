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
  simp [decide_eq_true_iff]
  rw [List.count_eq_of_count_filter_add_count_filter_not]
  simp [decide_eq_true_iff]
  have : List.count x (numbers.filter (λ y => y ∈ numbers ∧ ¬(y > 0))) = 0 := by
    rw [List.count_eq_zero_of_not_mem]
    intro h_mem
    rw [List.mem_filter] at h_mem
    have : ¬(x > 0) := h_mem.2.2
    linarith [h]
  rw [this]
  simp

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
      exact ⟨hx.1, hx.2⟩
    · constructor
      · simp [List.all_eq_true]
        intro x hx
        rw [List.mem_filter]
        exact ⟨hx, hx⟩
      · simp [List.all_eq_true]
        intro x hx
        rw [List.mem_filter] at hx
        have h_pos : x > 0 := hx.1
        exact count_filter_pos numbers x h_pos