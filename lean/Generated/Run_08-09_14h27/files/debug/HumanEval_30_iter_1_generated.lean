import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int): List Int :=
  numbers.filter (λ x => x > 0)

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

-- LLM HELPER
lemma filter_mem (l : List Int) (p : Int → Bool) (x : Int) : 
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  rw [List.mem_filter]

-- LLM HELPER
lemma all_filter_pos (l : List Int) : 
  (l.filter (λ x => x > 0)).all (λ x => x > 0) = true := by
  rw [List.all_eq_true]
  intros x h
  rw [filter_mem] at h
  exact h.2

-- LLM HELPER
lemma count_filter (l : List Int) (x : Int) : 
  x > 0 → (l.filter (λ y => y > 0)).count x = l.count x := by
  intro h
  rw [List.count_filter]
  simp only [decide_eq_true_eq]
  exact h

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · unfold spec
    constructor
    · -- result.all (λ x => x > 0 ∧ x ∈ numbers)
      rw [List.all_eq_true]
      intros x h
      rw [filter_mem] at h
      constructor
      · simp at h
        exact h.2
      · exact h.1
    constructor
    · -- numbers.all (λ x => x > 0 → x ∈ result)
      rw [List.all_eq_true]
      intros x h
      intro pos_x
      rw [filter_mem]
      constructor
      · exact h
      · simp
        exact pos_x
    · -- result.all (λ x => result.count x = numbers.count x)
      rw [List.all_eq_true]
      intros x h
      rw [filter_mem] at h
      simp at h
      exact count_filter numbers x h.2

-- #test implementation [(-1), 2, (-4), 5, 6] = [2, 5, 6]
-- #test implementation [5, 3, (-5), 2, (-3), 3, 9, 0, 123, 1, (-10)] = [5, 3, 2, 3, 9, 123, 1]