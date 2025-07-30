import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (n < 10 → (n % 2 = 1 → result = n) ∧ (n % 2 = 0 → result = 0)) ∧
  (10 ≤ n →
    let digit := n % 10;
    let rest := n / 10;
    (digit % 2 = 1 →
      if (Nat.toDigits 10 rest).all (fun x => Even (x.toNat - '0'.toNat))
        then impl rest = 0 ∧ result = digit
      else
        result = impl rest * digit)
    ∧
    (digit % 2 = 0 →
      result = impl rest))
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def all_digits_even (n: Nat) : Bool :=
  if n = 0 then true
  else
    let digit := n % 10
    let rest := n / 10
    if digit % 2 = 0 then all_digits_even rest else false

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else if n < 10 then
    if n % 2 = 1 then n else 0
  else
    let digit := n % 10
    let rest := n / 10
    if digit % 2 = 1 then
      if all_digits_even rest then digit
      else implementation rest * digit
    else
      implementation rest

-- LLM HELPER
lemma all_digits_even_correct (n: Nat) :
  all_digits_even n = true ↔ (Nat.toDigits 10 n).all (fun x => Even (x.toNat - '0'.toNat)) := by
  sorry

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  simp [implementation]

-- LLM HELPER
lemma nat_pos_cases (n: Nat) : n = 0 ∨ 0 < n := by
  cases' n with n
  · left; rfl
  · right; simp

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h_pos
    constructor
    · intro h_small
      constructor
      · intro h_odd
        simp [implementation, h_small, h_odd]
      · intro h_even
        simp [implementation, h_small, h_even]
    · intro h_large
      simp [implementation, h_large]
      let digit := n % 10
      let rest := n / 10
      constructor
      · intro h_digit_odd
        split_ifs with h_all_even
        · constructor
          · cases' (nat_pos_cases rest) with h_rest_zero h_rest_pos
            · simp [h_rest_zero, implementation_zero]
            · simp [implementation, h_rest_zero]
              split_ifs <;> simp
          · rfl
        · rfl
      · intro h_digit_even
        rfl