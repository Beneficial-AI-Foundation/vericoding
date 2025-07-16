import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(num: String) :=
-- spec
let spec (result: Int) :=
  let num_val (ch : Char) :=
    if ch.isDigit then
      (ch.toNat - '0'.toNat)
    else if ch.isUpper then
      ((ch.toNat - 'A'.toNat) + 10)
    else 0;
  0 < num.length →
  (
    let char_val := num_val num.toList[0]!;
    (Nat.Prime char_val →
      (1 < num.length → result = char_val + implementation (num.drop 1)) ∧
      (1 = num.length → result = char_val)) ∧
    (¬Nat.Prime char_val →
      (1 < num.length → result = implementation (num.drop 1)) ∧
      (1 = num.length → result = 0))
  )
-- program termination
∃ result, implementation num = result ∧
spec result

-- LLM HELPER
def num_val (ch : Char) : Nat :=
  if ch.isDigit then
    (ch.toNat - '0'.toNat)
  else if ch.isUpper then
    ((ch.toNat - 'A'.toNat) + 10)
  else 0

-- LLM HELPER
lemma string_drop_length_lt (s : String) : 0 < s.length → (s.drop 1).length < s.length := by
  intro h
  have h_nonempty : s ≠ "" := by
    intro h_eq
    rw [h_eq] at h
    simp at h
  exact String.length_drop_lt h_nonempty 1 (by norm_num)

def implementation (num: String) : Int :=
  if num.length = 0 then 0
  else
    let char_val := num_val num.toList[0]!
    if Nat.Prime char_val then
      if num.length = 1 then char_val
      else char_val + implementation (num.drop 1)
    else
      if num.length = 1 then 0
      else implementation (num.drop 1)
termination_by num.length
decreasing_by
  have h_pos : 0 < num.length := by
    by_contra h
    push_neg at h
    have h_eq : num.length = 0 := Nat.eq_zero_of_le_zero h
    simp [h_eq] at *
  exact string_drop_length_lt num h_pos

theorem correctness
(num: String)
: problem_spec implementation num
:= by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h_pos
    unfold implementation
    have char_val := num_val num.toList[0]!
    by_cases h_prime : Nat.Prime char_val
    · -- Case: Prime
      constructor
      · intro _
        by_cases h_len : num.length = 1
        · -- Prime, length = 1
          constructor
          · intro h_len_gt1
            rw [h_len] at h_len_gt1
            omega
          · intro h_len_eq1
            simp [char_val, h_prime, h_len]
        · -- Prime, length > 1
          constructor
          · intro h_len_gt1
            simp [char_val, h_prime, h_len]
          · intro h_len_eq1
            exact absurd h_len_eq1 h_len
      · intro h_contra
        exact absurd h_prime h_contra
    · -- Case: Not prime
      constructor
      · intro h_contra
        exact absurd h_contra h_prime
      · intro _
        by_cases h_len : num.length = 1
        · -- Not prime, length = 1
          constructor
          · intro h_len_gt1
            rw [h_len] at h_len_gt1
            omega
          · intro h_len_eq1
            simp [char_val, h_prime, h_len]
        · -- Not prime, length > 1
          constructor
          · intro h_len_gt1
            simp [char_val, h_prime, h_len]
          · intro h_len_eq1
            exact absurd h_len_eq1 h_len