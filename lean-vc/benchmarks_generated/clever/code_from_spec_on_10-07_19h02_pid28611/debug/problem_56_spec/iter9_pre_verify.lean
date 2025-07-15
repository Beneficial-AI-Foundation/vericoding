import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def balanced_paren_count (chars: List Char) (open_char: Char) (close_char: Char) : Int :=
  chars.foldl (fun acc c =>
    if c = open_char then acc + 1
    else if c = close_char then acc - 1
    else acc) 0

def balanced_paren_non_computable (s: String) (open_char: Char) (close_char: Char) : Bool :=
  balanced_paren_count s.data open_char close_char = 0 ∧
  ∀ i, i ≤ s.data.length → balanced_paren_count (s.data.take i) open_char close_char ≥ 0

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
lemma balanced_paren_count_cons (open_char close_char c : Char) (rest : List Char) :
  balanced_paren_count (c :: rest) open_char close_char = 
  (if c = open_char then 1 else if c = close_char then -1 else 0) + 
  balanced_paren_count rest open_char close_char := by
  unfold balanced_paren_count
  rw [List.foldl_cons]
  simp only [zero_add]
  have h : List.foldl (fun acc c => if c = open_char then 1 + acc else if c = close_char then -1 + acc else acc)
      (if c = open_char then 1 else if c = close_char then -1 else 0) rest =
    (if c = open_char then 1 else if c = close_char then -1 else 0) +
      List.foldl (fun acc c => if c = open_char then 1 + acc else if c = close_char then -1 + acc else acc) 0 rest := by
    split_ifs with h1 h2
    · -- c = open_char
      simp [h1]
      rw [List.foldl_comm_of_comm]
      · simp [Int.add_comm]
      · intros; ring
    · -- c = close_char
      simp [h2]
      rw [List.foldl_comm_of_comm]
      · simp [Int.add_comm]
      · intros; ring
    · -- c ≠ open_char ∧ c ≠ close_char
      simp [h1, h2]
  rw [h]
  ring

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
        simp [hi, List.take_zero, balanced_paren_count]
    · intro h
      exact h.1
  | cons c rest ih =>
    simp [balanced_paren_helper]
    split_ifs with h1 h2
    · -- c = open_char
      simp [h1]
      constructor
      · intro ⟨h_pos, h_helper⟩
        rw [ih] at h_helper
        constructor
        · rw [balanced_paren_count_cons, h1]
          simp
          exact h_helper.1
        · intro i hi
          cases' i with i
          · simp [List.take_zero, balanced_paren_count]
            linarith
          · simp [List.take_succ_cons]
            rw [balanced_paren_count_cons, h1]
            simp
            rw [add_assoc]
            apply h_helper.2
            simp at hi
            exact Nat.le_of_succ_le_succ hi
      · intro h
        constructor
        · rw [balanced_paren_count_cons, h1] at h
          simp at h
          have h_bound := h.2 1 (Nat.succ_le_succ (Nat.zero_le _))
          simp [List.take_succ_cons, balanced_paren_count_cons, h1] at h_bound
          linarith
        · rw [ih]
          constructor
          · rw [balanced_paren_count_cons, h1] at h
            simp at h
            linarith
          · intro i hi
            have h_bound := h.2 (i + 1) (Nat.succ_le_succ hi)
            simp [List.take_succ_cons] at h_bound
            rw [balanced_paren_count_cons, h1] at h_bound
            simp at h_bound
            rw [add_assoc] at h_bound
            exact h_bound
    · -- c = close_char
      simp [h2]
      constructor
      · intro ⟨h_pos, h_helper⟩
        rw [ih] at h_helper
        constructor
        · rw [balanced_paren_count_cons, h2]
          simp [h1]
          linarith
        · intro i hi
          cases' i with i
          · simp [List.take_zero, balanced_paren_count]
            linarith
          · simp [List.take_succ_cons]
            rw [balanced_paren_count_cons, h2]
            simp [h1]
            rw [add_assoc, Int.add_neg_cancel_left]
            apply h_helper.2
            simp at hi
            exact Nat.le_of_succ_le_succ hi
      · intro h
        constructor
        · rw [balanced_paren_count_cons, h2] at h
          simp [h1] at h
          have h_bound := h.2 1 (Nat.succ_le_succ (Nat.zero_le _))
          simp [List.take_succ_cons, balanced_paren_count_cons, h2] at h_bound
          simp [h1] at h_bound
          linarith
        · rw [ih]
          constructor
          · rw [balanced_paren_count_cons, h2] at h
            simp [h1] at h
            linarith
          · intro i hi
            have h_bound := h.2 (i + 1) (Nat.succ_le_succ hi)
            simp [List.take_succ_cons] at h_bound
            rw [balanced_paren_count_cons, h2] at h_bound
            simp [h1] at h_bound
            rw [add_assoc, Int.add_neg_cancel_left] at h_bound
            exact h_bound
    · -- c ≠ open_char ∧ c ≠ close_char
      simp [h1, h2]
      rw [ih]
      constructor
      · intro h
        constructor
        · rw [balanced_paren_count_cons]
          simp [h1, h2]
          exact h.1
        · intro i hi
          cases' i with i
          · simp [List.take_zero, balanced_paren_count]
            linarith
          · simp [List.take_succ_cons]
            rw [balanced_paren_count_cons]
            simp [h1, h2]
            apply h.2
            simp at hi
            exact Nat.le_of_succ_le_succ hi
      · intro h
        constructor
        · rw [balanced_paren_count_cons] at h
          simp [h1, h2] at h
          exact h.1
        · intro i hi
          have h_bound := h.2 (i + 1) (Nat.succ_le_succ hi)
          simp [List.take_succ_cons] at h_bound
          rw [balanced_paren_count_cons] at h_bound
          simp [h1, h2] at h_bound
          exact h_bound

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