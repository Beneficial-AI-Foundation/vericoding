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
lemma string_drop_length (s : String) (n : Nat) : n < s.length → (s.drop n).length = s.length - n := by
  intro h
  simp [String.drop, String.length]
  rw [List.length_drop]
  simp [String.toList]

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
  rw [string_drop_length]
  omega
  omega

theorem correctness
(num: String)
: problem_spec implementation num
:= by
  unfold problem_spec
  simp only [exists_prop]
  use implementation num
  constructor
  · rfl
  · intro h_pos
    simp [implementation]
    cases' h_eq : num.length with
    | zero => 
      exfalso
      rw [h_eq] at h_pos
      exact Nat.not_lt_zero 0 h_pos
    | succ n =>
      simp [h_eq]
      cases' h_digit : (num.toList[0]!).isDigit with
      | true =>
        simp [num_val, h_digit]
        cases' h_prime : Nat.Prime ((num.toList[0]!).toNat - 48) with
        | true =>
          simp [h_prime]
          constructor
          · intro h_prime_val
            constructor
            · intro h_len_gt1
              cases' n with
              | zero =>
                simp at h_len_gt1
              | succ m =>
                simp
                have h_drop_pos : 0 < (num.drop 1).length := by
                  rw [string_drop_length]
                  simp [h_eq]
                  omega
                  simp [h_eq]
                  omega
                exact (correctness (num.drop 1)).2 h_drop_pos
            · intro h_len_eq1
              cases' n with
              | zero => simp
              | succ m => simp at h_len_eq1
        | false =>
          simp [h_prime]
          constructor
          · intro h_prime_val
            exfalso
            exact h_prime h_prime_val
          · intro h_not_prime
            constructor
            · intro h_len_gt1
              cases' n with
              | zero =>
                simp at h_len_gt1
              | succ m =>
                simp
                have h_drop_pos : 0 < (num.drop 1).length := by
                  rw [string_drop_length]
                  simp [h_eq]
                  omega
                  simp [h_eq]
                  omega
                exact (correctness (num.drop 1)).2 h_drop_pos
            · intro h_len_eq1
              cases' n with
              | zero => simp
              | succ m => simp at h_len_eq1
      | false =>
        cases' h_upper : (num.toList[0]!).isUpper with
        | true =>
          simp [num_val, h_digit, h_upper]
          cases' h_prime : Nat.Prime ((num.toList[0]!).toNat - 65 + 10) with
          | true =>
            simp [h_prime]
            constructor
            · intro h_prime_val
              constructor
              · intro h_len_gt1
                cases' n with
                | zero =>
                  simp at h_len_gt1
                | succ m =>
                  simp
                  have h_drop_pos : 0 < (num.drop 1).length := by
                    rw [string_drop_length]
                    simp [h_eq]
                    omega
                    simp [h_eq]
                    omega
                  exact (correctness (num.drop 1)).2 h_drop_pos
              · intro h_len_eq1
                cases' n with
                | zero => simp
                | succ m => simp at h_len_eq1
          | false =>
            simp [h_prime]
            constructor
            · intro h_prime_val
              exfalso
              exact h_prime h_prime_val
            · intro h_not_prime
              constructor
              · intro h_len_gt1
                cases' n with
                | zero =>
                  simp at h_len_gt1
                | succ m =>
                  simp
                  have h_drop_pos : 0 < (num.drop 1).length := by
                    rw [string_drop_length]
                    simp [h_eq]
                    omega
                    simp [h_eq]
                    omega
                  exact (correctness (num.drop 1)).2 h_drop_pos
              · intro h_len_eq1
                cases' n with
                | zero => simp
                | succ m => simp at h_len_eq1
        | false =>
          simp [num_val, h_digit, h_upper]
          constructor
          · intro h_prime_val
            exfalso
            exact Nat.not_prime_zero h_prime_val
          · intro h_not_prime
            constructor
            · intro h_len_gt1
              cases' n with
              | zero =>
                simp at h_len_gt1
              | succ m =>
                simp
                have h_drop_pos : 0 < (num.drop 1).length := by
                  rw [string_drop_length]
                  simp [h_eq]
                  omega
                  simp [h_eq]
                  omega
                exact (correctness (num.drop 1)).2 h_drop_pos
            · intro h_len_eq1
              cases' n with
              | zero => simp
              | succ m => simp at h_len_eq1