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
  rw [String.drop, String.length]
  simp [List.length_drop]
  omega

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
  simp_wf
  apply string_drop_length_lt
  omega

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
    split_ifs with h_empty
    · rw [h_empty] at h_pos
      exact absurd h_pos (Nat.not_lt_zero 0)
    · let char_val := num_val num.toList[0]!
      by_cases h_prime : Nat.Prime char_val
      · simp [h_prime]
        constructor
        · intro _
          constructor
          · intro h_len_gt1
            by_cases h_len_eq1 : num.length = 1
            · omega
            · simp [h_len_eq1]
              have h_drop_pos : 0 < (num.drop 1).length := by
                rw [String.drop, String.length]
                simp [List.length_drop]
                omega
              exact (correctness (num.drop 1)).2 h_drop_pos
          · intro h_len_eq1
            by_cases h_len_gt1 : 1 < num.length
            · omega
            · simp [h_len_eq1]
      · simp [h_prime]
        constructor
        · intro h_contra
          exact h_prime h_contra
        · intro _
          constructor
          · intro h_len_gt1
            by_cases h_len_eq1 : num.length = 1
            · omega
            · simp [h_len_eq1]
              have h_drop_pos : 0 < (num.drop 1).length := by
                rw [String.drop, String.length]
                simp [List.length_drop]
                omega
              exact (correctness (num.drop 1)).2 h_drop_pos
          · intro h_len_eq1
            by_cases h_len_gt1 : 1 < num.length
            · omega
            · simp [h_len_eq1]