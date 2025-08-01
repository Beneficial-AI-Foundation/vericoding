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
  induction n using Nat.strong_induction_on with
  | h n ih =>
    simp [all_digits_even]
    split_ifs with h_zero
    · simp [h_zero, Nat.toDigits]
    · simp [Nat.toDigits_def]
      sorry

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  simp [implementation]

-- LLM HELPER
lemma nat_pos_cases (n: Nat) : n = 0 ∨ 0 < n := by
  cases' n with n
  · left; rfl
  · right; simp

-- LLM HELPER
lemma implementation_single_digit_odd (n: Nat) (h1: n < 10) (h2: n % 2 = 1) (h3: 0 < n) :
  implementation n = n := by
  simp [implementation]
  split_ifs with h_zero h_small
  · contradiction
  · simp [h2]
  · omega

-- LLM HELPER
lemma implementation_single_digit_even (n: Nat) (h1: n < 10) (h2: n % 2 = 0) (h3: 0 < n) :
  implementation n = 0 := by
  simp [implementation]
  split_ifs with h_zero h_small
  · contradiction
  · simp [h2]
  · omega

-- LLM HELPER
lemma implementation_multi_digit_odd_all_even (n: Nat) (h1: 10 ≤ n) (h2: n % 10 % 2 = 1) 
  (h3: all_digits_even (n / 10) = true) :
  implementation n = n % 10 := by
  simp [implementation]
  split_ifs with h_zero h_small
  · omega
  · omega
  · simp [h2, h3]

-- LLM HELPER
lemma implementation_multi_digit_odd_not_all_even (n: Nat) (h1: 10 ≤ n) (h2: n % 10 % 2 = 1) 
  (h3: all_digits_even (n / 10) = false) :
  implementation n = implementation (n / 10) * (n % 10) := by
  simp [implementation]
  split_ifs with h_zero h_small
  · omega
  · omega
  · simp [h2, h3]

-- LLM HELPER
lemma implementation_multi_digit_even (n: Nat) (h1: 10 ≤ n) (h2: n % 10 % 2 = 0) :
  implementation n = implementation (n / 10) := by
  simp [implementation]
  split_ifs with h_zero h_small
  · omega
  · omega
  · simp [h2]

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
        exact implementation_single_digit_odd n h_small h_odd h_pos
      · intro h_even
        exact implementation_single_digit_even n h_small h_even h_pos
    · intro h_large
      let digit := n % 10
      let rest := n / 10
      constructor
      · intro h_digit_odd
        by_cases h_all_even : all_digits_even rest = true
        · constructor
          · rw [all_digits_even_correct] at h_all_even
            sorry
          · exact implementation_multi_digit_odd_all_even n h_large h_digit_odd h_all_even
        · simp [h_all_even]
          exact implementation_multi_digit_odd_not_all_even n h_large h_digit_odd (by simp [h_all_even])
      · intro h_digit_even
        exact implementation_multi_digit_even n h_large h_digit_even