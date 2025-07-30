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
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]?.getD 0 % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]?.getD 0 % 2 = 0 ∧
  result[0]?.getD 0 = numbers[i]?.getD 0 ∧
  result[1]?.getD 0 = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]?.getD 0 % 2 = 1 ∨ numbers[i]?.getD 0 < numbers[j]?.getD 0)) ∧
  (∀ k, k < numbers.length → numbers[k]?.getD 0 % 2 = 0 → numbers[i]?.getD 0 ≤ numbers[k]?.getD 0));
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
lemma find_min_even_none_iff (numbers: List Nat) :
  find_min_even numbers = none ↔ ∀ i, i < numbers.length → numbers[i]?.getD 0 % 2 = 1 := by
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
        | zero => simp [List.get?]; exact Nat.mod_two_ne_zero.mp h_even
        | succ i' => 
          simp [List.get?]
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
      have h_even : numbers[i]?.getD 0 % 2 = 0 := Nat.mod_two_ne_one.mp h_odd
      have : find_min_even numbers = none := this (fun j hj => by
        by_contra h_not_odd
        have h_even_j : numbers[j]?.getD 0 % 2 = 0 := Nat.mod_two_ne_one.mp h_not_odd
        have : ∃ k, k < numbers.length ∧ numbers[k]?.getD 0 % 2 = 0 := ⟨j, hj, h_even_j⟩
        simp [find_min_even] at this)
      rw [this] at h
      simp at h
    · use idx
      constructor
      · induction numbers generalizing idx with
        | nil => simp [find_min_even_aux] at h
        | cons x xs ih =>
          simp [find_min_even_aux] at h
          split_ifs at h with h_even
          · split at h
            case h_1 h_rec =>
              simp at h
              cases h
              simp [List.length]
              exact Nat.zero_lt_succ _
            case h_2 min_val min_idx h_rec =>
              split_ifs at h with h_cmp
              · simp at h
                cases h
                simp [List.length]
                exact Nat.zero_lt_succ _
              · simp at h
                cases h
                simp [List.length]
                exact Nat.succ_lt_succ (ih h_rec)
          · simp [List.length]
            exact Nat.succ_lt_succ (ih h)
      constructor
      · induction numbers generalizing idx with
        | nil => simp [find_min_even_aux] at h
        | cons x xs ih =>
          simp [find_min_even_aux] at h
          split_ifs at h with h_even
          · split at h
            case h_1 h_rec =>
              simp at h
              cases h
              simp [List.get?]
              exact h_even
            case h_2 min_val min_idx h_rec =>
              split_ifs at h with h_cmp
              · simp at h
                cases h
                simp [List.get?]
                exact h_even
              · simp at h
                cases h
                exact ih h_rec
          · exact ih h
      constructor
      · simp [List.get?]
      constructor
      · simp [List.get?]
      constructor
      · intros j hj_lt hj_idx
        left
        induction numbers generalizing j with
        | nil => simp at hj_lt
        | cons x xs ih =>
          cases j with
          | zero => simp [List.get?]
          | succ j' => 
            simp [List.get?]
            apply ih
            · simp at hj_lt; exact Nat.lt_of_succ_lt_succ hj_lt
            · exact Nat.lt_of_succ_lt_succ hj_idx
      · intros k hk_lt hk_even
        exact Nat.le_refl _