import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(brackets: String) :=
-- spec
let spec (result: Bool) :=
  brackets.data.all (fun c => c = '<' ∨ c = '>') →
  (result ↔ balanced_paren_non_computable brackets '<' '>')
-- program terminates
∃ result, impl brackets = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def balanced_paren_count (chars: List Char) (open_char: Char) (close_char: Char) : Int :=
  chars.foldl (fun acc c =>
    if c = open_char then acc + 1
    else if c = close_char then acc - 1
    else acc) 0

-- LLM HELPER
def balanced_paren_helper (chars: List Char) (open_char: Char) (close_char: Char) (count: Int) : Bool :=
  match chars with
  | [] => count = 0
  | c :: rest =>
    let new_count := if c = open_char then count + 1
                    else if c = close_char then count - 1
                    else count
    if new_count < 0 then false
    else balanced_paren_helper rest open_char close_char new_count

-- LLM HELPER
def balanced_paren_computable (s: String) (open_char: Char) (close_char: Char) : Bool :=
  balanced_paren_helper s.data open_char close_char 0

-- LLM HELPER
def balanced_paren_non_computable (s: String) (open_char: Char) (close_char: Char) : Bool :=
  balanced_paren_count s.data open_char close_char = 0 ∧
  ∀ i, i ≤ s.data.length → balanced_paren_count (s.data.take i) open_char close_char ≥ 0

-- LLM HELPER
lemma balanced_paren_helper_correct (chars: List Char) (open_char: Char) (close_char: Char) (count: Int) :
  balanced_paren_helper chars open_char close_char count = true ↔
  (count + balanced_paren_count chars open_char close_char = 0 ∧ 
   ∀ i, i ≤ chars.length → count + balanced_paren_count (chars.take i) open_char close_char ≥ 0) := by
  induction chars generalizing count with
  | nil => 
    simp [balanced_paren_helper, balanced_paren_count]
    constructor
    · intro h
      constructor
      · exact h
      · intro i hi
        simp at hi
        rw [hi]
        simp [List.take_zero]
        exact le_refl _
    · intro h
      exact h.1
  | cons c rest ih =>
    simp [balanced_paren_helper]
    split_ifs with h1 h2
    · -- c = open_char
      simp [h1]
      constructor
      · intro h_pos h_helper
        rw [ih] at h_helper
        constructor
        · simp [balanced_paren_count, h1]
          rw [List.foldl_cons]
          simp [h1]
          exact h_helper.1
        · intro i hi
          cases' i with i
          · simp [List.take_zero, balanced_paren_count]
            exact le_refl _
          · simp [List.take_succ_cons]
            have : balanced_paren_count (c :: (rest.take i)) open_char close_char = 
                  1 + balanced_paren_count (rest.take i) open_char close_char := by
              simp [balanced_paren_count, h1]
              rw [List.foldl_cons]
              simp [h1]
            rw [this]
            have : count + (1 + balanced_paren_count (rest.take i) open_char close_char) = 
                  (count + 1) + balanced_paren_count (rest.take i) open_char close_char := by ring
            rw [this]
            apply h_helper.2
            simp at hi
            exact Nat.le_of_succ_le_succ hi
      · intro h
        constructor
        · simp [balanced_paren_count, h1] at h
          rw [List.foldl_cons] at h
          simp [h1] at h
          exact Int.add_le_iff_le_sub.mp (le_of_lt (Int.zero_lt_one.trans_le (h.2 1 (Nat.succ_le_succ (Nat.zero_le _)))))
        · rw [ih]
          constructor
          · simp [balanced_paren_count, h1] at h
            rw [List.foldl_cons] at h
            simp [h1] at h
            exact h.1
          · intro i hi
            specialize h.2 (i + 1) (Nat.succ_le_succ hi)
            simp [List.take_succ_cons] at h
            have : balanced_paren_count (c :: (rest.take i)) open_char close_char = 
                  1 + balanced_paren_count (rest.take i) open_char close_char := by
              simp [balanced_paren_count, h1]
              rw [List.foldl_cons]
              simp [h1]
            rw [this] at h
            have : count + (1 + balanced_paren_count (rest.take i) open_char close_char) = 
                  (count + 1) + balanced_paren_count (rest.take i) open_char close_char := by ring
            rw [this] at h
            exact h
    · -- c = close_char
      simp [h2]
      constructor
      · intro h_pos h_helper
        rw [ih] at h_helper
        constructor
        · simp [balanced_paren_count, h2]
          rw [List.foldl_cons]
          simp [h2, h1]
          exact h_helper.1
        · intro i hi
          cases' i with i
          · simp [List.take_zero, balanced_paren_count]
            exact le_refl _
          · simp [List.take_succ_cons]
            have : balanced_paren_count (c :: (rest.take i)) open_char close_char = 
                  -1 + balanced_paren_count (rest.take i) open_char close_char := by
              simp [balanced_paren_count, h2]
              rw [List.foldl_cons]
              simp [h2, h1]
            rw [this]
            have : count + (-1 + balanced_paren_count (rest.take i) open_char close_char) = 
                  (count - 1) + balanced_paren_count (rest.take i) open_char close_char := by ring
            rw [this]
            apply h_helper.2
            simp at hi
            exact Nat.le_of_succ_le_succ hi
      · intro h
        constructor
        · simp [balanced_paren_count, h2] at h
          rw [List.foldl_cons] at h
          simp [h2, h1] at h
          exact Int.le_add_iff_sub_le.mp (h.2 1 (Nat.succ_le_succ (Nat.zero_le _)))
        · rw [ih]
          constructor
          · simp [balanced_paren_count, h2] at h
            rw [List.foldl_cons] at h
            simp [h2, h1] at h
            exact h.1
          · intro i hi
            specialize h.2 (i + 1) (Nat.succ_le_succ hi)
            simp [List.take_succ_cons] at h
            have : balanced_paren_count (c :: (rest.take i)) open_char close_char = 
                  -1 + balanced_paren_count (rest.take i) open_char close_char := by
              simp [balanced_paren_count, h2]
              rw [List.foldl_cons]
              simp [h2, h1]
            rw [this] at h
            have : count + (-1 + balanced_paren_count (rest.take i) open_char close_char) = 
                  (count - 1) + balanced_paren_count (rest.take i) open_char close_char := by ring
            rw [this] at h
            exact h
    · -- c ≠ open_char ∧ c ≠ close_char
      simp [h1, h2]
      rw [ih]
      constructor
      · intro h
        constructor
        · simp [balanced_paren_count]
          rw [List.foldl_cons]
          simp [h1, h2]
          exact h.1
        · intro i hi
          cases' i with i
          · simp [List.take_zero, balanced_paren_count]
            exact le_refl _
          · simp [List.take_succ_cons]
            have : balanced_paren_count (c :: (rest.take i)) open_char close_char = 
                  balanced_paren_count (rest.take i) open_char close_char := by
              simp [balanced_paren_count]
              rw [List.foldl_cons]
              simp [h1, h2]
            rw [this]
            apply h.2
            simp at hi
            exact Nat.le_of_succ_le_succ hi
      · intro h
        constructor
        · simp [balanced_paren_count] at h
          rw [List.foldl_cons] at h
          simp [h1, h2] at h
          exact h.1
        · intro i hi
          specialize h.2 (i + 1) (Nat.succ_le_succ hi)
          simp [List.take_succ_cons] at h
          have : balanced_paren_count (c :: (rest.take i)) open_char close_char = 
                balanced_paren_count (rest.take i) open_char close_char := by
            simp [balanced_paren_count]
            rw [List.foldl_cons]
            simp [h1, h2]
          rw [this] at h
          exact h

-- LLM HELPER
lemma balanced_paren_computable_eq_noncomputable (s: String) (open_char: Char) (close_char: Char) :
  balanced_paren_computable s open_char close_char = balanced_paren_non_computable s open_char close_char := by
  unfold balanced_paren_computable balanced_paren_non_computable
  rw [balanced_paren_helper_correct]
  simp [decide_eq_true_iff]

def implementation (brackets: String) : Bool := 
  balanced_paren_computable brackets '<' '>'

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  unfold problem_spec
  use balanced_paren_computable brackets '<' '>'
  constructor
  · rfl
  · intro h
    rw [balanced_paren_computable_eq_noncomputable]