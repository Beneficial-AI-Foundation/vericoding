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

-- LLM HELPER
lemma drop_length_lt (s : String) (h : 1 < s.length) : (s.drop 1).length < s.length := by
  simp [String.length_drop]
  omega

theorem correctness
(num: String)
: problem_spec implementation num
:= by
  unfold problem_spec
  simp only [exists_prop]
  constructor
  · rfl
  · intro h_pos
    simp [implementation]
    split_ifs with h_empty h_prime h_len1 h_len2
    · contradiction
    · simp [num_val]
      constructor
      · intro h_prime_val
        constructor
        · intro h_len_gt1
          simp [h_len1] at h_len_gt1
        · intro h_len_eq1
          rfl
      · intro h_not_prime
        simp [Nat.Prime] at h_not_prime h_prime_val
        contradiction
    · simp [num_val]
      constructor
      · intro h_prime_val
        constructor
        · intro h_len_gt1
          simp [h_len1] at h_len_gt1
        · intro h_len_eq1
          rfl
      · intro h_not_prime
        simp [Nat.Prime] at h_not_prime h_prime_val
        contradiction
    · simp [num_val]
      constructor
      · intro h_prime_val
        constructor
        · intro h_len_gt1
          congr 1
          apply correctness
        · intro h_len_eq1
          simp [h_len2] at h_len_eq1
          omega
      · intro h_not_prime
        simp [Nat.Prime] at h_not_prime h_prime_val
        contradiction
    · simp [num_val]
      constructor
      · intro h_prime_val
        simp [Nat.Prime] at h_not_prime h_prime_val
        contradiction
      · intro h_not_prime
        constructor
        · intro h_len_gt1
          apply correctness
        · intro h_len_eq1
          simp [h_len2] at h_len_eq1
          omega
termination_by num.length