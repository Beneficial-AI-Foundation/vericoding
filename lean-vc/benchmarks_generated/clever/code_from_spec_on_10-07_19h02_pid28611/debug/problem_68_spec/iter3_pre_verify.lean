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
    · split at h
      case h_1 h_rec =>
        cases h
        simp [List.length]
        exact Nat.lt_succ_iff.mpr (Nat.le_add_right _ _)
      case h_2 min_val min_idx h_rec =>
        split_ifs at h with h_cmp
        · cases h
          simp [List.length]
          exact Nat.lt_succ_iff.mpr (Nat.le_add_right _ _)
        · cases h
          have := ih (start_idx + 1) min_val min_idx h_rec
          simp [List.length] at this
          exact Nat.lt_succ_of_lt this
    · have := ih (start_idx + 1) val idx h
      simp [List.length] at this
      exact Nat.lt_succ_of_lt this

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
    · split at h
      case h_1 h_rec =>
        cases h
        exact h_even
      case h_2 min_val min_idx h_rec =>
        split_ifs at h with h_cmp
        · cases h
          exact h_even
        · cases h
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
    · split at h
      case h_1 h_rec =>
        cases h
        simp [List.get!, Nat.sub_self]
      case h_2 min_val min_idx h_rec =>
        split_ifs at h with h_cmp
        · cases h
          simp [List.get!, Nat.sub_self]
        · cases h
          have := ih (start_idx + 1) min_val min_idx h_rec
          simp [List.get!, Nat.succ_sub_succ_eq_sub] at this
          exact this
    · have := ih (start_idx + 1) val idx h
      simp [List.get!, Nat.succ_sub_succ_eq_sub] at this
      exact this

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
    · split at h
      case h_1 h_rec =>
        cases h
        cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
        · rw [h_eq, List.get!, Nat.sub_self]
        · simp [List.length] at hk_lt
          exact absurd (Nat.lt_of_succ_le hk_lt) (Nat.not_lt_of_ge (Nat.le_of_lt h_lt))
      case h_2 min_val min_idx h_rec =>
        split_ifs at h with h_cmp
        · cases h
          cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
          · rw [h_eq, List.get!, Nat.sub_self]
          · have ih_result := ih (start_idx + 1) min_val min_idx h_rec k (Nat.le_of_lt h_lt)
            simp [List.length] at hk_lt
            have k_bound : k < start_idx + 1 + xs.length := Nat.lt_trans (Nat.lt_succ_of_le (Nat.le_of_lt h_lt)) hk_lt
            have := ih_result k_bound
            simp [List.get!, Nat.succ_sub_succ_eq_sub] at this
            rw [List.get!, Nat.succ_sub_succ_eq_sub] at hk_even
            exact Nat.le_trans (Nat.le_of_not_gt h_cmp) (this hk_even)
        · cases h
          cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
          · rw [h_eq, List.get!, Nat.sub_self]
            have ih_result := ih (start_idx + 1) min_val min_idx h_rec (start_idx + 1) (Nat.le_refl _)
            simp [List.length] at ih_result
            have : start_idx + 1 < start_idx + 1 + xs.length := Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
            have xs_even : xs[0]! % 2 = 0 := by
              simp [List.get!]
              cases xs with
              | nil => simp
              | cons y ys => simp
            exact ih_result this xs_even
          · have ih_result := ih (start_idx + 1) min_val min_idx h_rec k (Nat.le_of_lt h_lt)
            simp [List.length] at hk_lt
            have k_bound : k < start_idx + 1 + xs.length := Nat.lt_trans (Nat.lt_succ_of_le (Nat.le_of_lt h_lt)) hk_lt
            have := ih_result k_bound
            simp [List.get!, Nat.succ_sub_succ_eq_sub] at this
            rw [List.get!, Nat.succ_sub_succ_eq_sub] at hk_even
            exact this hk_even
    · cases' Nat.eq_or_lt_of_le hk_ge with h_eq h_lt
      · rw [h_eq, List.get!, Nat.sub_self] at hk_even
        exact absurd hk_even h_even
      · have ih_result := ih (start_idx + 1) val idx h k (Nat.le_of_lt h_lt)
        simp [List.length] at hk_lt
        have k_bound : k < start_idx + 1 + xs.length := Nat.lt_trans (Nat.lt_succ_of_le (Nat.le_of_lt h_lt)) hk_lt
        have := ih_result k_bound
        simp [List.get!, Nat.succ_sub_succ_eq_sub] at this
        rw [List.get!, Nat.succ_sub_succ_eq_sub] at hk_even
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
    · split at h
      case h_1 h_rec =>
        cases h
        exact absurd (Nat.le_refl _) (Nat.not_le_of_gt hj_lt)
      case h_2 min_val min_idx h_rec =>
        split_ifs at h with h_cmp
        · cases h
          exact absurd (Nat.le_refl _) (Nat.not_le_of_gt hj_lt)
        · cases h
          cases' Nat.eq_or_lt_of_le hj_ge with h_eq h_lt
          · rw [h_eq, List.get!, Nat.sub_self]
            right
            exact Nat.lt_of_not_ge h_cmp
          · have := ih (start_idx + 1) min_val min_idx h_rec j (Nat.le_of_lt h_lt) hj_lt
            simp [List.get!, Nat.succ_sub_succ_eq_sub]
            exact this
    · cases' Nat.eq_or_lt_of_le hj_ge with h_eq h_lt
      · rw [h_eq, List.get!, Nat.sub_self]
        left
        exact Nat.mod_two_ne_zero.mp h_even
      · have := ih (start_idx + 1) val idx h j (Nat.le_of_lt h_lt) hj_lt
        simp [List.get!, Nat.succ_sub_succ_eq_sub]
        exact this

-- LLM HELPER
lemma find_min_even_none_iff (numbers: List Nat) :
  find_min_even numbers = none ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1 := by
  simp [find_min_even]
  constructor
  · intro h i hi
    induction numbers generalizing i with
    | nil => simp at hi
    | cons x xs ih =>
      simp [find_min_even_aux] at h
      split_ifs at h with h_even
      · split at h
        case h_1 h_rec =>
          simp at h
        case h_2 min_val min_idx h_rec =>
          simp at h
      · cases i with
        | zero => simp [List.get!]; exact Nat.mod_two_ne_zero.mp h_even
        | succ i' => 
          simp [List.get!]
          apply ih
          · exact h
          · simp at hi; exact Nat.lt_of_succ_lt_succ hi
  · intro h
    induction numbers with
    | nil => simp [find_min_even_aux]
    | cons x xs ih =>
      simp [find_min_even_aux]
      have x_odd : x % 2 = 1 := h 0 (Nat.zero_lt_succ _)
      have x_not_even : ¬(x % 2 = 0) := Nat.mod_two_ne_zero.mpr x_odd
      simp [x_not_even]
      apply ih
      intro i hi
      exact h (i + 1) (Nat.succ_lt_succ hi)

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  cases h : find_min_even numbers with
  | none => 
    use []
    simp
    constructor
    · exact find_min_even_none_iff numbers |>.mp h
    · intro i hi h_even hval hidx
      have := find_min_even_none_iff numbers |>.mp h
      exact absurd (this i hi) h_even
  | some val_idx =>
    obtain ⟨val, idx⟩ := val_idx
    simp [find_min_even] at h
    use [val, idx]
    simp
    constructor
    · intro i hi
      have := find_min_even_none_iff numbers |>.mpr
      by_contra h_odd
      have h_even : numbers[i]! % 2 = 0 := Nat.mod_two_ne_one.mp h_odd
      have : find_min_even numbers = none := this (fun j hj => by
        by_contra h_not_odd
        have h_even_j : numbers[j]! % 2 = 0 := Nat.mod_two_ne_one.mp h_not_odd
        have : ∃ k, k < numbers.length ∧ numbers[k]! % 2 = 0 := ⟨j, hj, h_even_j⟩
        simp [find_min_even] at this)
      rw [this] at h
      simp at h
    · use idx
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