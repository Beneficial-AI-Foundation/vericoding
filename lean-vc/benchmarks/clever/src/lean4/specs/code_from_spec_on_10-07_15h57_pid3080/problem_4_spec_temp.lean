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
lemma implementation_eq (numbers: List Rat) : 
  implementation numbers = 
  if numbers.length = 0 then 0 else
    (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / (numbers.length * numbers.length) := by
  rfl

-- LLM HELPER
lemma div_nonneg_of_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  exact div_nonneg ha (le_of_lt hb)

-- LLM HELPER
lemma abs_nonneg_rat (x : Rat) : 0 ≤ |x| := abs_nonneg x

-- LLM HELPER
lemma sum_map_abs_nonneg (numbers : List Rat) : 
  0 ≤ (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum := by
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact abs_nonneg_rat _

-- LLM HELPER
lemma length_pos_of_pos {α : Type*} (l : List α) (h : 0 < l.length) : 0 < (l.length : Rat) := by
  exact Rat.coe_nat_pos.mpr h

-- LLM HELPER
lemma length_mul_length_pos (numbers : List Rat) (h : 0 < numbers.length) : 
  0 < (numbers.length : Rat) * (numbers.length : Rat) := by
  have h1 : 0 < (numbers.length : Rat) := length_pos_of_pos numbers h
  exact mul_pos h1 h1

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec
  simp only [exists_prop]
  use implementation numbers
  constructor
  · rfl
  · intro h
    rw [implementation_eq]
    simp only [if_pos (ne_of_gt h)]
    constructor
    · apply div_nonneg_of_nonneg
      · exact sum_map_abs_nonneg numbers
      · exact length_mul_length_pos numbers h
    · have h_nonzero : (numbers.length : Rat) ≠ 0 := ne_of_gt (length_pos_of_pos numbers h)
      rw [div_mul_cancel]
      · ring
      · apply mul_ne_zero h_nonzero h_nonzero