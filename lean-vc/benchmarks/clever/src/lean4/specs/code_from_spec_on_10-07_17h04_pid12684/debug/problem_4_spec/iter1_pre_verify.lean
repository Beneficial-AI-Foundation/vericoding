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
lemma abs_nonneg (x : Rat) : 0 ≤ |x| := abs_nonneg x

-- LLM HELPER
lemma sum_nonneg_of_nonneg {l : List Rat} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.sum_cons]
    apply add_nonneg
    · exact h a (List.mem_cons_self a l)
    · exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

-- LLM HELPER
lemma list_map_abs_nonneg (numbers : List Rat) :
  ∀ x ∈ numbers.map (fun x => |x * numbers.length - numbers.sum|), 0 ≤ x := by
  intro x hx
  simp [List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact abs_nonneg _

-- LLM HELPER
lemma div_nonneg_of_nonneg_pos {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [div_nonneg_iff]
  left
  exact ⟨ha, hb⟩

-- LLM HELPER
lemma nat_cast_mul_pos {n : ℕ} (hn : 0 < n) : (0 : Rat) < n * n := by
  simp [Nat.cast_mul]
  exact mul_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hn)

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec
  simp [implementation]
  split_ifs with h
  · use 0
    simp
    intro h_pos
    rw [List.length_eq_zero] at h
    rw [h] at h_pos
    simp at h_pos
  · use (numbers.map (fun x => |x * numbers.length - numbers.sum|)).sum / (numbers.length * numbers.length)
    constructor
    · rfl
    · intro h_pos
      constructor
      · apply div_nonneg_of_nonneg_pos
        · exact sum_nonneg_of_nonneg (list_map_abs_nonneg numbers)
        · exact nat_cast_mul_pos h_pos
      · rw [div_mul_cancel]
        exact ne_of_gt (nat_cast_mul_pos h_pos)