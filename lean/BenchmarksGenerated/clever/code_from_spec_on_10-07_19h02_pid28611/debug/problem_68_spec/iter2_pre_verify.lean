import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(numbers: List Nat) :=
-- spec
let spec (result: List Nat) :=
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]! % 2 = 0 ∧
  result[0]! = numbers[i]! ∧
  result[1]! = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_even_aux (numbers: List Nat) (idx: Nat) : Option (Nat × Nat) :=
  match numbers with
  | [] => none
  | x :: xs => 
    if x % 2 = 0 then
      match find_min_even_aux xs (idx + 1) with
      | none => some (x, idx)
      | some (min_val, min_idx) => 
        if x ≤ min_val then some (x, idx) else some (min_val, min_idx)
    else
      find_min_even_aux xs (idx + 1)

-- LLM HELPER
def find_min_even (numbers: List Nat) : Option (Nat × Nat) :=
  find_min_even_aux numbers 0

def implementation (numbers: List Nat) : List Nat := 
  match find_min_even numbers with
  | none => []
  | some (val, idx) => [val, idx]

-- LLM HELPER
lemma find_min_even_aux_length (numbers: List Nat) (start_idx: Nat) :
  ∀ val idx, find_min_even_aux numbers start_idx = some (val, idx) → 
  idx < start_idx + numbers.length := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih => 
    intros val idx h
    simp [find_min_even_aux] at h
    split_ifs at h with h_even
    · split at h with h_rec
      · simp at h
        cases h
        simp [Nat.lt_add_iff_pos_left]
      · obtain ⟨min_val, min_idx⟩ := h_rec
        simp at h
        split_ifs at h with h_cmp
        · simp at h
          cases h
          simp [Nat.lt_add_iff_pos_left]
        · simp at h
          cases h
          have := ih (start_idx + 1) min_val min_idx h_rec
          simp at this
          exact Nat.lt_trans this (Nat.lt_add_one _)
    · have := ih (start_idx + 1) val idx h
      simp at this
      exact Nat.lt_trans this (Nat.lt_add_one _)

-- LLM HELPER
lemma find_min_even_aux_even (numbers: List Nat) (start_idx: Nat) :
  ∀ val idx, find_min_even_aux numbers start_idx = some (val, idx) → 
  val % 2 = 0 := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih => 
    intros val idx h
    simp [find_min_even_aux] at h
    split_ifs at h with h_even
    · split at h with h_rec
      · simp at h
        cases h
        exact h_even
      · obtain ⟨min_val, min_idx⟩ := h_rec
        simp at h
        split_ifs at h with h_cmp
        · simp at h
          cases h
          exact h_even
        · simp at h
          cases h
          exact ih (start_idx + 1) min_val min_idx h_rec
    · exact ih (start_idx + 1) val idx h

-- LLM HELPER
lemma find_min_even_aux_correct_val (numbers: List Nat) (start_idx: Nat) :
  ∀ val idx, find_min_even_aux numbers start_idx = some (val, idx) → 
  numbers[idx - start_idx]! = val := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih => 
    intros val idx h
    simp [find_min_even_aux] at h
    split_ifs at h with h_even
    · split at h with h_rec
      · simp at h
        cases h
        simp [List.get!, Nat.sub_self]
      · obtain ⟨min_val, min_idx⟩ := h_rec
        simp at h
        split_ifs at h with h_cmp
        · simp at h
          cases h
          simp [List.get!, Nat.sub_self]
        · simp at h
          cases h
          have := ih (start_idx + 1) min_val min_idx h_rec
          simp at this
          convert this using 1
          simp [List.get!]
          rw [Nat.succ_sub_succ_eq_sub]
    · have := ih (start_idx + 1) val idx h
      simp at this
      convert this using 1
      simp [List.get!]
      rw [Nat.succ_sub_succ_eq_sub]

-- LLM HELPER
lemma find_min_even_aux_minimal (numbers: List Nat) (start_idx: Nat) :
  ∀ val idx, find_min_even_aux numbers start_idx = some (val, idx) → 
  ∀ k, start_idx ≤ k → k < start_idx + numbers.length → 
  numbers[k - start_idx]! % 2 = 0 → val ≤ numbers[k - start_idx]! := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih => 
    intros val idx h k hk_ge hk_lt hk_even
    simp [find_min_even_aux] at h
    split_ifs at h with h_even
    · split at h with h_rec
      · simp at h
        cases h
        simp at hk_lt
        cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
        · rw [h_eq]
          simp [List.get!]
        · have : k >= start_idx + 1 := Nat.le_of_lt h_lt
          have : k < start_idx + (xs.length + 1) := hk_lt
          simp at this
          have k_bound : k < start_idx + 1 := Nat.lt_of_le_of_lt this (Nat.le_refl _)
          exact absurd (Nat.le_of_succ_le_succ k_bound) (Nat.not_le_of_gt h_lt)
      · obtain ⟨min_val, min_idx⟩ := h_rec
        simp at h
        split_ifs at h with h_cmp
        · simp at h
          cases h
          simp at hk_lt
          cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
          · rw [h_eq]
            simp [List.get!]
          · have min_le := ih (start_idx + 1) min_val min_idx h_rec k (Nat.le_of_lt h_lt) hk_lt
            simp at min_le
            have conv_eq : numbers[k - start_idx]! = xs[k - (start_idx + 1)]! := by
              simp [List.get!]
              rw [Nat.succ_sub_succ_eq_sub]
            rw [conv_eq] at hk_even
            have := min_le hk_even
            rw [← conv_eq] at this
            exact Nat.le_trans (Nat.le_of_not_gt (fun h => h_cmp h)) this
        · simp at h
          cases h
          simp at hk_lt
          cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
          · rw [h_eq]
            simp [List.get!]
            have min_le := ih (start_idx + 1) min_val min_idx h_rec (start_idx + 1) (Nat.le_refl _)
            simp at min_le
            have : start_idx + 1 < start_idx + 1 + xs.length := by simp [Nat.lt_add_iff_pos_left]
            have : xs[0]! % 2 = 0 := by
              simp [List.get!]
              cases xs with
              | nil => simp
              | cons y ys => simp [List.get!]
            specialize min_le this this
            exact min_le
          · have min_le := ih (start_idx + 1) min_val min_idx h_rec k (Nat.le_of_lt h_lt) hk_lt
            simp at min_le
            have conv_eq : numbers[k - start_idx]! = xs[k - (start_idx + 1)]! := by
              simp [List.get!]
              rw [Nat.succ_sub_succ_eq_sub]
            rw [conv_eq] at hk_even
            exact min_le hk_even
    · have min_le := ih (start_idx + 1) val idx h k
      simp at hk_lt
      cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
      · rw [h_eq] at hk_even
        simp [List.get!] at hk_even
        exact absurd hk_even h_even
      · have := min_le (Nat.le_of_lt h_lt) hk_lt
        simp at this
        have conv_eq : numbers[k - start_idx]! = xs[k - (start_idx + 1)]! := by
          simp [List.get!]
          rw [Nat.succ_sub_succ_eq_sub]
        rw [conv_eq] at hk_even
        exact this hk_even

-- LLM HELPER
lemma find_min_even_aux_first_even (numbers: List Nat) (start_idx: Nat) :
  ∀ val idx, find_min_even_aux numbers start_idx = some (val, idx) → 
  ∀ j, start_idx ≤ j → j < idx → numbers[j - start_idx]! % 2 = 1 ∨ val < numbers[j - start_idx]! := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih => 
    intros val idx h j hj_ge hj_lt
    simp [find_min_even_aux] at h
    split_ifs at h with h_even
    · split at h with h_rec
      · simp at h
        cases h
        exact absurd (Nat.le_refl _) (Nat.not_le_of_gt hj_lt)
      · obtain ⟨min_val, min_idx⟩ := h_rec
        simp at h
        split_ifs at h with h_cmp
        · simp at h
          cases h
          exact absurd (Nat.le_refl _) (Nat.not_le_of_gt hj_lt)
        · simp at h
          cases h
          cases' Nat.eq_or_lt_of_le hj_ge with h_eq h_lt
          · rw [h_eq] at hj_lt
            simp [List.get!]
            right
            exact Nat.lt_of_not_ge h_cmp
          · have := ih (start_idx + 1) min_val min_idx h_rec j (Nat.le_of_lt h_lt) hj_lt
            simp at this
            have conv_eq : numbers[j - start_idx]! = xs[j - (start_idx + 1)]! := by
              simp [List.get!]
              rw [Nat.succ_sub_succ_eq_sub]
            rw [conv_eq]
            exact this
    · have := ih (start_idx + 1) val idx h j
      cases' Nat.eq_or_lt_of_le hj_ge with h_eq h_lt
      · rw [h_eq] at hj_lt
        simp [List.get!]
        left
        exact Nat.mod_two_ne_zero.mp h_even
      · have := this (Nat.le_of_lt h_lt) hj_lt
        simp at this
        have conv_eq : numbers[j - start_idx]! = xs[j - (start_idx + 1)]! := by
          simp [List.get!]
          rw [Nat.succ_sub_succ_eq_sub]
        rw [conv_eq]
        exact this

-- LLM HELPER
lemma find_min_even_none_iff (numbers: List Nat) :
  find_min_even numbers = none ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1 := by
  simp [find_min_even]
  sorry

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  cases h : find_min_even numbers with
  | none => 
    use []
    simp
    constructor
    · simp
      exact find_min_even_none_iff numbers |>.mp h
    · simp
      intro i hi h_even hval hidx
      have := find_min_even_none_iff numbers |>.mp h
      exact absurd (this i hi) h_even
  | some val_idx =>
    obtain ⟨val, idx⟩ := val_idx
    simp [find_min_even] at h
    use [val, idx]
    simp
    constructor
    · simp
      intro i hi
      have := find_min_even_none_iff numbers |>.mpr
      by_contra h_odd
      have h_even : ∃ i, i < numbers.length ∧ numbers[i]! % 2 = 0 := 
        ⟨i, hi, Nat.mod_two_ne_one.mp h_odd⟩
      simp [find_min_even] at this
      have := this (fun j hj => by
        by_contra h_not_odd
        have h_even_j : numbers[j]! % 2 = 0 := Nat.mod_two_ne_one.mp h_not_odd
        exact h_even ⟨j, hj, h_even_j⟩)
      rw [this] at h
      simp at h
    · simp
      use idx
      constructor
      · exact find_min_even_aux_length numbers 0 val idx h
      constructor
      · exact find_min_even_aux_even numbers 0 val idx h
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · intros j hj_lt hj_idx
        have := find_min_even_aux_first_even numbers 0 val idx h j (Nat.zero_le _) hj_idx
        simp at this
        exact this
      · intros k hk_lt hk_even
        have := find_min_even_aux_minimal numbers 0 val idx h k (Nat.zero_le _) hk_lt hk_even
        simp at this
        exact this