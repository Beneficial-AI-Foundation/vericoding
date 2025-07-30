import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat):=
0 < numbers.length →
0 ≤ result ∧
result * numbers.length * numbers.length =
(numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum;
-- program terminates
∃ result, implementation numbers = result ∧
-- return value satisfies spec
spec result

def implementation (numbers: List Rat) : Rat := 
  if numbers.length = 0 then 0 else
  (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / (numbers.length * numbers.length)

-- LLM HELPER
lemma length_pos_of_pos {l : List Rat} (h : 0 < l.length) : (0 : Rat) < l.length := by
  exact Nat.cast_pos.mpr h

-- LLM HELPER
lemma sum_abs_nonneg (l : List Rat) : 0 ≤ (l.map abs).sum := by
  induction l with
  | nil => simp
  | cons h t ih => 
    simp [List.map_cons, List.sum_cons]
    apply add_nonneg
    exact abs_nonneg h
    exact ih

-- LLM HELPER
lemma sum_abs_deviation_nonneg (numbers : List Rat) : 0 ≤ (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum := by
  apply List.sum_nonneg
  intro x hx
  simp at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact abs_nonneg _

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp [implementation]
  by_cases h : numbers.length = 0
  · simp [h]
    use 0
    simp
    intro h_pos
    simp at h_pos
    rw [h] at h_pos
    exact absurd h_pos (Nat.lt_irrefl 0)
  · push_neg at h
    have h_pos : 0 < numbers.length := Nat.pos_of_ne_zero h
    simp [if_neg h]
    use (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / (numbers.length * numbers.length)
    constructor
    · rfl
    · intro h_pos_len
      constructor
      · apply div_nonneg
        · exact sum_abs_deviation_nonneg numbers
        · apply mul_pos
          · exact length_pos_of_pos h_pos_len
          · exact length_pos_of_pos h_pos_len
      · have h_ne_zero : (numbers.length : Rat) * numbers.length ≠ 0 := by
          apply ne_of_gt
          apply mul_pos
          · exact length_pos_of_pos h_pos_len
          · exact length_pos_of_pos h_pos_len
        rw [div_mul_cancel _ h_ne_zero]