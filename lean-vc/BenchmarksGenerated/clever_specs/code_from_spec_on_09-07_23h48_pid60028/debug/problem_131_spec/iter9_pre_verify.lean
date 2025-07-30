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
lemma allDigitsEven_empty_list : ([] : List Char).all (fun _ => True) = true := by
  simp [List.all_nil]

-- LLM HELPER
lemma allDigitsEven_correct (n: Nat) :
  allDigitsEven n = true ↔ (Nat.toDigits 10 n).all (fun x => Even (x.toNat - '0'.toNat)) := by
  constructor
  · intro h
    induction n using Nat.strong_induction with
    | ind n ih =>
      by_cases h_zero : n = 0
      · simp [h_zero, Nat.toDigits_zero, List.all_nil]
      · by_cases h_small : n < 10
        · simp [Nat.toDigits_of_lt_base (by norm_num : (0 : Nat) < 10) h_small, List.all_cons, List.all_nil]
          unfold allDigitsEven at h
          simp [h_zero] at h
          unfold Even
          simp only [Char.toNat_sub_toNat_of_le]
          exact h
        · simp [Nat.toDigits_of_ge_base (by norm_num : (1 : Nat) < 10) h_small, List.all_cons]
          unfold allDigitsEven at h
          simp [h_zero] at h
          constructor
          · unfold Even
            simp only [Char.toNat_sub_toNat_of_le]
            exact h.1
          · exact ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h_zero) (by norm_num)) h.2
  · intro h
    induction n using Nat.strong_induction with
    | ind n ih =>
      by_cases h_zero : n = 0
      · simp [h_zero, allDigitsEven]
      · by_cases h_small : n < 10
        · unfold allDigitsEven
          simp [h_zero]
          simp [Nat.toDigits_of_lt_base (by norm_num : (0 : Nat) < 10) h_small, List.all_cons, List.all_nil] at h
          unfold Even at h
          simp only [Char.toNat_sub_toNat_of_le] at h
          exact h
        · unfold allDigitsEven
          simp [h_zero]
          simp [Nat.toDigits_of_ge_base (by norm_num : (1 : Nat) < 10) h_small, List.all_cons] at h
          constructor
          · unfold Even at h
            simp only [Char.toNat_sub_toNat_of_le] at h
            exact h.1
          · exact ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h_zero) (by norm_num)) h.2

-- LLM HELPER
lemma implementation_terminates (n: Nat) : n ≥ 10 → n / 10 < n := by
  intro h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero (ne_of_gt (Nat.lt_of_succ_le h))) (by norm_num)

-- LLM HELPER
lemma nat_mod_two_cases (n: Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have h := Nat.mod_two_eq_zero_or_one n
  exact h

-- LLM HELPER
lemma implementation_zero_when_all_even (n: Nat) : allDigitsEven n = true → implementation n = 0 := by
  intro h
  induction n using Nat.strong_induction with
  | ind n ih =>
    unfold implementation
    by_cases h_zero : n = 0
    · simp [h_zero]
    · by_cases h_small : n < 10
      · simp [h_zero, h_small]
        have h_even : n % 2 = 0 := by
          unfold allDigitsEven at h
          simp [h_zero] at h
          exact h
        simp [h_even]
      · simp [h_zero, h_small]
        let digit := n % 10
        let rest := n / 10
        have h_rest_even : allDigitsEven rest = true := by
          unfold allDigitsEven at h
          simp [h_zero] at h
          exact h.2
        have h_digit_even : digit % 2 = 0 := by
          unfold allDigitsEven at h
          simp [h_zero] at h
          exact h.1
        simp [h_digit_even]
        have h_rest_lt : rest < n := implementation_terminates n (Nat.not_lt.mp h_small)
        exact ih rest h_rest_lt h_rest_even

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
          have cases := nat_mod_two_cases n
          cases cases with
          | inl h => simp [h]
          | inr h => simp [h] at h_even; contradiction
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
        by_cases h_all_even : allDigitsEven rest
        · simp [h_all_even]
          constructor
          · rw [← allDigitsEven_correct] at h_all_even
            exact implementation_zero_when_all_even rest h_all_even
          · rfl
        · simp [h_all_even]
      · intro h_digit_even
        unfold implementation
        simp [h_large]
        have h_not_small : ¬(n < 10) := Nat.not_lt.mpr h_large
        simp [h_not_small]
        let digit := n % 10
        let rest := n / 10
        have h_not_odd : ¬(digit % 2 = 1) := by
          have cases := nat_mod_two_cases digit
          cases cases with
          | inl h => simp [h]
          | inr h => simp [h] at h_digit_even; contradiction
        simp [h_not_odd]