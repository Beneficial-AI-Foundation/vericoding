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
  if numbers.length = 0 then 0 
  else (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / (numbers.length * numbers.length)

-- LLM HELPER
lemma list_sum_nonneg_of_nonneg (l : List Rat) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp [List.sum_cons]
    apply add_nonneg
    · exact h head (List.mem_cons_self head tail)
    · exact ih (fun x hx => h x (List.mem_cons_of_mem head hx))

-- LLM HELPER
lemma abs_nonneg_rat (x : Rat) : 0 ≤ |x| := abs_nonneg x

-- LLM HELPER
lemma div_nonneg_of_nonneg_and_pos (a b : Rat) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  exact div_nonneg ha (le_of_lt hb)

-- LLM HELPER
lemma list_length_pos_iff_nonempty (l : List Rat) : 0 < l.length ↔ l ≠ [] := by
  constructor
  · intro h
    intro h_eq
    rw [h_eq] at h
    simp at h
  · intro h
    cases' l with head tail
    · contradiction
    · simp

-- LLM HELPER
lemma nat_cast_mul_rat (n m : ℕ) : (n * m : Rat) = (n : Rat) * (m : Rat) := by
  exact Nat.cast_mul n m

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp [implementation]
  split_ifs with h
  · use 0
    constructor
    · rfl
    · intro h_pos
      rw [List.length_eq_zero] at h
      rw [h] at h_pos
      simp at h_pos
  · use (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / (numbers.length * numbers.length)
    constructor
    · rfl
    · intro h_pos
      constructor
      · -- Show 0 ≤ result
        apply div_nonneg_of_nonneg_and_pos
        · apply list_sum_nonneg_of_nonneg
          intro x hx
          simp at hx
          obtain ⟨y, hy_mem, hy_eq⟩ := hx
          rw [← hy_eq]
          exact abs_nonneg_rat _
        · -- Show 0 < numbers.length * numbers.length
          have h_len_pos : 0 < numbers.length := h_pos
          have h_len_pos_rat : (0 : Rat) < numbers.length := by
            exact Nat.cast_pos.mpr h_len_pos
          exact mul_pos h_len_pos_rat h_len_pos_rat
      · -- Show the main equation
        have h_ne_zero : numbers.length ≠ 0 := by
          intro h_zero
          rw [h_zero] at h_pos
          exact Nat.lt_irrefl 0 h_pos
        have h_len_pos_rat : (0 : Rat) < numbers.length := by
          exact Nat.cast_pos.mpr h_pos
        have h_len_sq_pos : (0 : Rat) < numbers.length * numbers.length := by
          exact mul_pos h_len_pos_rat h_len_pos_rat
        rw [div_mul_cancel]
        exact ne_of_gt h_len_sq_pos