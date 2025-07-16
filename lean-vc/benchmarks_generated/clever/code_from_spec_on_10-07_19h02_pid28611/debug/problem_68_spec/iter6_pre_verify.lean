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
lemma find_min_even_aux_none_iff (numbers: List Nat) (start_idx: Nat) :
  find_min_even_aux numbers start_idx = none ↔ 
  ∀ i, i < numbers.length → numbers[i]?.getD 0 % 2 = 1 := by
  induction numbers generalizing start_idx with
  | nil => simp [find_min_even_aux]
  | cons x xs ih =>
    simp [find_min_even_aux]
    split_ifs with h_even
    · simp
      constructor
      · intro h
        split at h
        · simp at h
        · intro i hi
          cases i with
          | zero => simp [List.get?]; exact h_even
          | succ i' => 
            simp [List.get?]
            have h_rec : find_min_even_aux xs (start_idx + 1) = none := by
              simp at h
              cases h_aux : find_min_even_aux xs (start_idx + 1)
              · rfl
              · simp [h_aux] at h
            exact (ih (start_idx + 1) |>.mp h_rec) i' (Nat.lt_of_succ_lt_succ hi)
      · intro h
        exfalso
        exact absurd h_even (Nat.mod_two_ne_zero.mpr (h 0 (Nat.zero_lt_succ _)))
    · simp [ih]
      constructor
      · intro h i hi
        cases i with
        | zero => simp [List.get?]; exact Nat.mod_two_ne_zero.mp h_even
        | succ i' => 
          simp [List.get?]
          exact h i' (Nat.lt_of_succ_lt_succ hi)
      · intro h
        intro i hi
        exact h (i + 1) (Nat.succ_lt_succ hi)

-- LLM HELPER
lemma find_min_even_none_iff (numbers: List Nat) :
  find_min_even numbers = none ↔ ∀ i, i < numbers.length → numbers[i]?.getD 0 % 2 = 1 := by
  simp [find_min_even]
  exact find_min_even_aux_none_iff numbers 0

-- LLM HELPER
lemma find_min_even_aux_some_correct (numbers: List Nat) (start_idx: Nat) (val idx: Nat) :
  find_min_even_aux numbers start_idx = some (val, idx) →
  ∃ i, i < numbers.length ∧ 
    numbers[i]?.getD 0 % 2 = 0 ∧
    val = numbers[i]?.getD 0 ∧
    idx = start_idx + i ∧
    (∀ j, j < numbers.length → j < i → numbers[j]?.getD 0 % 2 = 1 ∨ numbers[i]?.getD 0 < numbers[j]?.getD 0) ∧
    (∀ k, k < numbers.length → numbers[k]?.getD 0 % 2 = 0 → numbers[i]?.getD 0 ≤ numbers[k]?.getD 0) := by
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
    · exact find_min_even_none_iff numbers |>.mp h
    · intro i hi h_even hval hidx hj hk
      have := find_min_even_none_iff numbers |>.mp h
      exact absurd h_even (Nat.mod_two_ne_zero.mpr (this i hi))
  | some val_idx =>
    obtain ⟨val, idx⟩ := val_idx
    use [val, idx]
    simp
    constructor
    · intro h_contra
      have := find_min_even_none_iff numbers |>.mpr h_contra
      rw [this] at h
      simp at h
    · use 0
      constructor
      · by_cases h_empty : numbers.length = 0
        · simp [h_empty] at h
          simp [find_min_even, find_min_even_aux] at h
        · exact Nat.pos_of_ne_zero h_empty
      constructor
      · cases numbers with
        | nil => simp [find_min_even, find_min_even_aux] at h
        | cons x xs =>
          simp [find_min_even, find_min_even_aux] at h
          split_ifs at h with h_even
          · split at h
            · simp at h
              cases h
              simp [List.get?]
              exact h_even
            · simp at h
              split_ifs at h with h_cmp
              · simp at h
                cases h
                simp [List.get?]
                exact h_even
              · sorry
          · sorry
      constructor
      · simp [List.get?]
      constructor
      · simp [List.get?]
      constructor
      · intro j hj_lt hj_lt_zero
        exfalso
        exact Nat.not_lt_zero j hj_lt_zero
      · intro k hk_lt hk_even
        sorry