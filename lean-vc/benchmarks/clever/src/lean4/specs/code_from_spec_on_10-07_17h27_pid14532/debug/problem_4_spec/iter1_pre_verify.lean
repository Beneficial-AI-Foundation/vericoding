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
lemma list_sum_map_abs_nonneg (numbers: List Rat) :
  0 ≤ (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum := by
  apply List.sum_nonneg
  intro x hx
  simp at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [←hxy]
  exact abs_nonneg _

-- LLM HELPER
lemma div_mul_cancel_of_pos {a b : Rat} (hb : 0 < b) : a / b * b = a := by
  rw [div_mul_cancel]
  exact ne_of_gt hb

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp [implementation]
  split_ifs with h
  · -- Case: numbers.length = 0
    use 0
    constructor
    · rfl
    · intro h_pos
      rw [h] at h_pos
      exact absurd h_pos (lt_irrefl 0)
  · -- Case: numbers.length ≠ 0
    have h_pos : 0 < numbers.length := Nat.pos_of_ne_zero h
    use (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / (numbers.length * numbers.length)
    constructor
    · rfl
    · intro _
      constructor
      · -- Show 0 ≤ result
        apply div_nonneg
        · exact list_sum_map_abs_nonneg numbers
        · apply mul_pos
          · exact Nat.cast_pos.mpr h_pos
          · exact Nat.cast_pos.mpr h_pos
      · -- Show result * numbers.length * numbers.length = sum
        rw [div_mul_cancel]
        apply ne_of_gt
        apply mul_pos
        · exact Nat.cast_pos.mpr h_pos
        · exact Nat.cast_pos.mpr h_pos