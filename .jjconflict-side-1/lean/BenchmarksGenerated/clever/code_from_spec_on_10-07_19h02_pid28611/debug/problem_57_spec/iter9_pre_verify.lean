import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let non_ordered := ∃ i j,
i < numbers.length - 1 ∧
j < numbers.length - 1 ∧
(numbers[i]! < numbers[i+1]!) ∧
(numbers[j+1]! < numbers[j]!);
-- spec
let spec (result: Bool) :=
  1 < numbers.length →
  result ↔ ¬non_ordered;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def is_monotonic_increasing (numbers: List Int) : Bool :=
  numbers.zip (numbers.tail) |>.all (fun (a, b) => a ≤ b)

-- LLM HELPER
def is_monotonic_decreasing (numbers: List Int) : Bool :=
  numbers.zip (numbers.tail) |>.all (fun (a, b) => a ≥ b)

def implementation (numbers: List Int) : Bool := 
  is_monotonic_increasing numbers || is_monotonic_decreasing numbers

-- LLM HELPER
lemma zip_mem_iff (numbers: List Int) (i : Nat) :
  i < numbers.length - 1 → (numbers[i]!, numbers[i+1]!) ∈ numbers.zip numbers.tail := by
  intro h
  rw [List.mem_zip]
  use i
  constructor
  · have h_len : numbers.length > 0 := by
      linarith
    exact List.get_mem numbers i (by linarith)
  · have h_tail_len : numbers.tail.length = numbers.length - 1 := List.length_tail numbers
    rw [h_tail_len] at h
    exact List.get_mem numbers.tail i h

-- LLM HELPER
lemma tail_get_eq (numbers: List Int) (i : Nat) :
  i < numbers.length - 1 → numbers.tail[i]! = numbers[i+1]! := by
  intro h
  simp only [List.get_tail]

-- LLM HELPER
lemma zip_mem_exists (numbers: List Int) (a b : Int) :
  (a, b) ∈ numbers.zip numbers.tail → 
  ∃ i, i < numbers.length - 1 ∧ (numbers[i]!, numbers[i+1]!) = (a, b) := by
  intro h_mem
  rw [List.mem_zip] at h_mem
  obtain ⟨i, ha, hb⟩ := h_mem
  have h_i_bound : i < numbers.length - 1 := by
    rw [List.length_tail] at hb
    by_cases h_empty : numbers.length = 0
    · simp at hb
      linarith
    · rw [Nat.sub_zero] at h_empty
      exact List.get_mem_iff.mp hb
  use i
  constructor
  · exact h_i_bound
  · simp only [List.get_tail] at hb
    rw [← List.get_mem_iff.mp ha, ← List.get_mem_iff.mp hb]

-- LLM HELPER
lemma non_ordered_iff_not_monotonic (numbers: List Int) :
  1 < numbers.length →
  ((is_monotonic_increasing numbers || is_monotonic_decreasing numbers) = true ↔
   ¬(∃ i j, i < numbers.length - 1 ∧ j < numbers.length - 1 ∧ 
    (numbers[i]! < numbers[i+1]!) ∧ (numbers[j+1]! < numbers[j]!))) := by
  intro h
  constructor
  · intro h_monotonic h_non_ordered
    obtain ⟨i, j, hi_lt, hj_lt, h_inc, h_dec⟩ := h_non_ordered
    cases' Bool.or_eq_true_iff.mp h_monotonic with h_inc_true h_dec_true
    · unfold is_monotonic_increasing at h_inc_true
      rw [List.all_eq_true] at h_inc_true
      have h_i_in : (numbers[i]!, numbers[i+1]!) ∈ numbers.zip numbers.tail := zip_mem_iff numbers i hi_lt
      have h_le : numbers[i]! ≤ numbers[i+1]! := by
        have h_match := h_inc_true (numbers[i]!, numbers[i+1]!) h_i_in
        simp at h_match
        exact of_decide_eq_true h_match
      exact not_le.mpr h_inc h_le
    · unfold is_monotonic_decreasing at h_dec_true
      rw [List.all_eq_true] at h_dec_true
      have h_j_in : (numbers[j]!, numbers[j+1]!) ∈ numbers.zip numbers.tail := zip_mem_iff numbers j hj_lt
      have h_ge : numbers[j]! ≥ numbers[j+1]! := by
        have h_match := h_dec_true (numbers[j]!, numbers[j+1]!) h_j_in
        simp at h_match
        exact of_decide_eq_true h_match
      have h_lt : numbers[j+1]! < numbers[j]! := h_dec
      exact not_le.mpr h_lt h_ge
  · intro h_no_non_ordered
    by_contra h_not_monotonic
    rw [Bool.not_eq_true] at h_not_monotonic
    have h_not_inc : is_monotonic_increasing numbers = false := by
      rw [Bool.or_eq_false_iff] at h_not_monotonic
      exact h_not_monotonic.1
    have h_not_dec : is_monotonic_decreasing numbers = false := by
      rw [Bool.or_eq_false_iff] at h_not_monotonic
      exact h_not_monotonic.2
    unfold is_monotonic_increasing at h_not_inc
    unfold is_monotonic_decreasing at h_not_dec
    rw [List.all_eq_false] at h_not_inc h_not_dec
    push_neg at h_not_inc h_not_dec
    obtain ⟨⟨ai, bi⟩, hi_mem, hi_not⟩ := h_not_inc
    obtain ⟨⟨aj, bj⟩, hj_mem, hj_not⟩ := h_not_dec
    simp at hi_not hj_not
    have hi_exists := zip_mem_exists numbers ai bi hi_mem
    have hj_exists := zip_mem_exists numbers aj bj hj_mem
    obtain ⟨i, hi_lt, hi_eq⟩ := hi_exists
    obtain ⟨j, hj_lt, hj_eq⟩ := hj_exists
    have h_inc : numbers[i]! < numbers[i+1]! := by
      rw [← hi_eq] at hi_not
      simp at hi_not
      exact Int.lt_of_not_le hi_not
    have h_dec : numbers[j+1]! < numbers[j]! := by
      rw [← hj_eq] at hj_not
      simp at hj_not
      exact Int.lt_of_not_le hj_not
    exact h_no_non_ordered ⟨i, j, hi_lt, hj_lt, h_inc, h_dec⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  simp only [exists_prop]
  use is_monotonic_increasing numbers || is_monotonic_decreasing numbers
  constructor
  · rfl
  · intro h
    exact (non_ordered_iff_not_monotonic numbers h)