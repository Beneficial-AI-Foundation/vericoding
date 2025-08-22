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
  all_digits_even n = true ↔ (Nat.toDigits 10 n).all (fun x => decide (Even (x.toNat - '0'.toNat))) = true := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold all_digits_even
    by_cases h_zero : n = 0
    · simp [h_zero, Nat.toDigits]
    · simp [h_zero]
      have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
      rw [Nat.toDigits_cons h_pos (by norm_num)]
      simp [List.all_cons]
      constructor
      · intro h
        constructor
        · simp [Char.toNat]
          norm_cast
          exact h.1
        · rw [← ih]
          · exact h.2
          · exact Nat.div_lt_self h_pos (by norm_num)
      · intro ⟨h1, h2⟩
        simp [Char.toNat] at h1
        norm_cast at h1
        constructor
        · exact h1
        · rw [ih]
          · exact h2
          · exact Nat.div_lt_self h_pos (by norm_num)

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  unfold implementation
  simp

-- LLM HELPER
lemma nat_pos_cases (n: Nat) : n = 0 ∨ 0 < n := by
  cases' n with n
  · left; rfl
  · right; simp

-- LLM HELPER
lemma implementation_single_digit_odd (n: Nat) (h1: n < 10) (h2: n % 2 = 1) (h3: 0 < n) :
  implementation n = n := by
  unfold implementation
  simp [Ne.symm (ne_of_gt h3), h1, h2]

-- LLM HELPER
lemma implementation_single_digit_even (n: Nat) (h1: n < 10) (h2: n % 2 = 0) (h3: 0 < n) :
  implementation n = 0 := by
  unfold implementation
  simp [Ne.symm (ne_of_gt h3), h1, h2]

-- LLM HELPER
lemma implementation_multi_digit_odd_all_even (n: Nat) (h1: 10 ≤ n) (h2: n % 10 % 2 = 1) 
  (h3: all_digits_even (n / 10) = true) :
  implementation n = n % 10 := by
  unfold implementation
  have h_pos : 0 < n := Nat.pos_of_ne_zero (ne_of_gt (Nat.lt_of_succ_le h1))
  simp [Ne.symm (ne_of_gt h_pos), not_lt.mpr h1, h2, h3]

-- LLM HELPER
lemma implementation_multi_digit_odd_not_all_even (n: Nat) (h1: 10 ≤ n) (h2: n % 10 % 2 = 1) 
  (h3: all_digits_even (n / 10) = false) :
  implementation n = implementation (n / 10) * (n % 10) := by
  unfold implementation
  have h_pos : 0 < n := Nat.pos_of_ne_zero (ne_of_gt (Nat.lt_of_succ_le h1))
  simp [Ne.symm (ne_of_gt h_pos), not_lt.mpr h1, h2, h3]

-- LLM HELPER
lemma implementation_multi_digit_even (n: Nat) (h1: 10 ≤ n) (h2: n % 10 % 2 = 0) :
  implementation n = implementation (n / 10) := by
  unfold implementation
  have h_pos : 0 < n := Nat.pos_of_ne_zero (ne_of_gt (Nat.lt_of_succ_le h1))
  simp [Ne.symm (ne_of_gt h_pos), not_lt.mpr h1, h2]

-- LLM HELPER
lemma all_digits_even_zero (n: Nat) : all_digits_even n = true → implementation n = 0 := by
  intro h
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_zero : n = 0
    · simp [h_zero, implementation_zero]
    · by_cases h_small : n < 10
      · unfold all_digits_even at h
        simp [h_zero] at h
        have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
        have h_even : n % 10 % 2 = 0 := by
          by_contra h_odd
          push_neg at h_odd
          have h_mod_odd : n % 10 % 2 = 1 := Nat.mod_two_eq_one_iff_odd.mpr (Nat.odd_iff_not_even.mpr (fun h_ev => h_odd (Nat.even_iff_two_dvd.mp h_ev)))
          simp [h_mod_odd] at h
        have h_n_even : n % 2 = 0 := by
          have : n = n % 10 := Nat.mod_eq_of_lt h_small
          rw [this]
          exact h_even
        exact implementation_single_digit_even n h_small h_n_even h_pos
      · push_neg at h_small
        have h_large : 10 ≤ n := h_small
        unfold all_digits_even at h
        simp [h_zero] at h
        by_cases h_digit_even : n % 10 % 2 = 0
        · have h_rest_even : all_digits_even (n / 10) = true := by
            simp [h_digit_even] at h
            exact h
          rw [implementation_multi_digit_even n h_large h_digit_even]
          apply ih
          · exact Nat.div_lt_self (Nat.pos_of_ne_zero h_zero) (by norm_num)
          · exact h_rest_even
        · simp [h_digit_even] at h

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
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
        rw [all_digits_even_correct] at *
        by_cases h_all_even : (Nat.toDigits 10 rest).all (fun x => decide (Even (x.toNat - '0'.toNat))) = true
        · constructor
          · have h_rest_even : all_digits_even rest = true := by
              rw [all_digits_even_correct]
              exact h_all_even
            exact all_digits_even_zero rest h_rest_even
          · have h_rest_even : all_digits_even rest = true := by
              rw [all_digits_even_correct]
              exact h_all_even
            exact implementation_multi_digit_odd_all_even n h_large h_digit_odd h_rest_even
        · have h_rest_not_even : all_digits_even rest = false := by
            rw [all_digits_even_correct]
            simp at h_all_even
            exact h_all_even
          exact implementation_multi_digit_odd_not_all_even n h_large h_digit_odd h_rest_not_even
      · intro h_digit_even
        exact implementation_multi_digit_even n h_large h_digit_even