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
def Even (n : Nat) : Prop := n % 2 = 0

-- LLM HELPER
def allDigitsEven (n: Nat) : Bool :=
  if n = 0 then true
  else (n % 10) % 2 = 0 && allDigitsEven (n / 10)

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else if n < 10 then
    if n % 2 = 1 then n else 0
  else
    let digit := n % 10
    let rest := n / 10
    if digit % 2 = 1 then
      if allDigitsEven rest then digit
      else implementation rest * digit
    else
      implementation rest

-- LLM HELPER
lemma allDigitsEven_correct (n: Nat) :
  allDigitsEven n = true ↔ (Nat.toDigits 10 n).all (fun x => Even (x.toNat - '0'.toNat)) := by
  sorry

-- LLM HELPER
lemma implementation_terminates (n: Nat) : n ≥ 10 → n / 10 < n := by
  intro h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero (ne_of_gt (Nat.lt_of_succ_le h))) (by norm_num)

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
        unfold implementation
        simp [h_small, h_odd]
      · intro h_even
        unfold implementation
        simp [h_small, h_even]
        have h_not_odd : ¬(n % 2 = 1) := by
          rw [← Nat.mod_two_eq_zero_or_one] at h_even
          cases h_even with
          | inl h => simp [h]
          | inr h => simp [h]
        simp [h_not_odd]
    · intro h_large
      constructor
      · intro h_digit_odd
        unfold implementation
        simp [h_large]
        have h_not_small : ¬(n < 10) := Nat.not_lt.mpr h_large
        simp [h_not_small]
        let digit := n % 10
        let rest := n / 10
        simp [h_digit_odd]
        split_ifs with h_all_even
        · constructor
          · by_cases h_rest_zero : rest = 0
            · simp [h_rest_zero]
              unfold implementation
              simp
            · have h_rest_pos : 0 < rest := by
                have : n ≥ 10 := h_large
                have : n / 10 > 0 := Nat.div_pos this (by norm_num)
                exact this
              rw [allDigitsEven_correct] at h_all_even
              have spec_rest := correctness rest
              unfold problem_spec at spec_rest
              cases spec_rest with
              | mk result_rest h_rest =>
                cases h_rest with
                | mk h_eq h_spec =>
                  rw [← h_eq]
                  exact sorry
          · rfl
        · rfl
      · intro h_digit_even
        unfold implementation
        simp [h_large]
        have h_not_small : ¬(n < 10) := Nat.not_lt.mpr h_large
        simp [h_not_small]
        let digit := n % 10
        let rest := n / 10
        have h_not_odd : ¬(digit % 2 = 1) := by
          rw [← Nat.mod_two_eq_zero_or_one] at h_digit_even
          cases h_digit_even with
          | inl h => simp [h]
          | inr h => simp [h]
        simp [h_not_odd]