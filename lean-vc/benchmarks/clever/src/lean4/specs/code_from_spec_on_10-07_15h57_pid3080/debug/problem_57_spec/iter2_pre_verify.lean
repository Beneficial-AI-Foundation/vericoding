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
def is_non_decreasing (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    if a ≤ b then is_non_decreasing (b :: rest)
    else false

-- LLM HELPER
def is_non_increasing (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    if a ≥ b then is_non_increasing (b :: rest)
    else false

def implementation (numbers: List Int) : Bool := 
  is_non_decreasing numbers || is_non_increasing numbers

-- LLM HELPER
lemma is_non_decreasing_iff_monotone (l : List Int) :
  is_non_decreasing l = true ↔ 
  ∀ i, i < l.length - 1 → l[i]! ≤ l[i+1]! := by
  induction l with
  | nil => simp [is_non_decreasing]
  | cons a tail ih =>
    cases tail with
    | nil => simp [is_non_decreasing]
    | cons b rest =>
      simp [is_non_decreasing]
      constructor
      · intro h
        intro i hi
        cases i with
        | zero => 
          simp at h
          exact h.1
        | succ i' =>
          simp at h
          simp at hi
          have h_rec := ih.mp h.2
          exact h_rec i' hi
      · intro h
        constructor
        · exact h 0 (by simp)
        · apply ih.mpr
          intro i hi
          exact h (i + 1) (by simp; exact hi)

-- LLM HELPER
lemma is_non_increasing_iff_monotone (l : List Int) :
  is_non_increasing l = true ↔ 
  ∀ i, i < l.length - 1 → l[i]! ≥ l[i+1]! := by
  induction l with
  | nil => simp [is_non_increasing]
  | cons a tail ih =>
    cases tail with
    | nil => simp [is_non_increasing]
    | cons b rest =>
      simp [is_non_increasing]
      constructor
      · intro h
        intro i hi
        cases i with
        | zero => 
          simp at h
          exact h.1
        | succ i' =>
          simp at h
          simp at hi
          have h_rec := ih.mp h.2
          exact h_rec i' hi
      · intro h
        constructor
        · exact h 0 (by simp)
        · apply ih.mpr
          intro i hi
          exact h (i + 1) (by simp; exact hi)

-- LLM HELPER
lemma non_ordered_iff_not_monotone (numbers : List Int) :
  (∃ i j, i < numbers.length - 1 ∧ j < numbers.length - 1 ∧ 
   (numbers[i]! < numbers[i+1]!) ∧ (numbers[j+1]! < numbers[j]!)) ↔
  ¬(∀ i, i < numbers.length - 1 → numbers[i]! ≤ numbers[i+1]!) ∧
  ¬(∀ i, i < numbers.length - 1 → numbers[i]! ≥ numbers[i+1]!) := by
  constructor
  · intro ⟨i, j, hi, hj, h_inc, h_dec⟩
    constructor
    · intro h_mono
      have := h_mono j hj
      linarith [h_dec]
    · intro h_mono
      have := h_mono i hi
      linarith [h_inc]
  · intro ⟨h_not_inc, h_not_dec⟩
    push_neg at h_not_inc h_not_dec
    obtain ⟨i, hi, h_inc⟩ := h_not_inc
    obtain ⟨j, hj, h_dec⟩ := h_not_dec
    use i, j
    exact ⟨hi, hj, h_inc, h_dec⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  simp only [Bool.or_eq_true_iff]
  use (is_non_decreasing numbers || is_non_increasing numbers)
  constructor
  · rfl
  · intro h
    constructor
    · intro h_impl
      rw [non_ordered_iff_not_monotone]
      constructor
      · rw [← is_non_decreasing_iff_monotone]
        cases h_impl with
        | inl h1 => exact h1
        | inr h2 => 
          by_contra h_contra
          rw [← is_non_increasing_iff_monotone] at h2
          rw [is_non_decreasing_iff_monotone] at h_contra
          have : ∀ i, i < numbers.length - 1 → numbers[i]! = numbers[i+1]! := by
            intro i hi
            have h_ge := h2 i hi
            have h_le := h_contra i hi
            linarith
          rw [← is_non_increasing_iff_monotone] at this
          simp at this
      · rw [← is_non_increasing_iff_monotone]
        cases h_impl with
        | inl h1 => 
          by_contra h_contra
          rw [← is_non_decreasing_iff_monotone] at h1
          rw [is_non_increasing_iff_monotone] at h_contra
          have : ∀ i, i < numbers.length - 1 → numbers[i]! = numbers[i+1]! := by
            intro i hi
            have h_le := h1 i hi
            have h_ge := h_contra i hi
            linarith
          rw [← is_non_decreasing_iff_monotone] at this
          simp at this
        | inr h2 => exact h2
    · intro h_not_non_ordered
      rw [non_ordered_iff_not_monotone] at h_not_non_ordered
      push_neg at h_not_non_ordered
      cases h_not_non_ordered with
      | inl h1 => 
        left
        rw [is_non_decreasing_iff_monotone]
        exact h1
      | inr h2 => 
        right
        rw [is_non_increasing_iff_monotone]
        exact h2