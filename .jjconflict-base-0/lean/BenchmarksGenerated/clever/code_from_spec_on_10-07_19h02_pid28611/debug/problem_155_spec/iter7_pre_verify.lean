import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Int → Int × Int)
-- inputs
(num: Int) :=
-- spec
let spec (result: Int × Int) :=
  let (even_count, odd_count) := result;
  let numAbs := |num|.toNat;
  let numBy10 := numAbs/10;
  let (even_count', odd_count') := impl numBy10;
  (result = impl numAbs) ∧
  (0 ≤ num → (Even num ↔ 1 + even_count' = even_count) ∧ (Odd num ↔ even_count' = even_count)) ∧
  (0 ≤ num → (Odd num ↔ 1 + odd_count' = odd_count) ∧ (Even num ↔ odd_count' = odd_count));
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def count_even_odd_digits (n : Nat) : Nat × Nat :=
  if n = 0 then (1, 0)
  else
    let digit := n % 10
    let (even_rest, odd_rest) := count_even_odd_digits (n / 10)
    if digit % 2 = 0 then (even_rest + 1, odd_rest)
    else (even_rest, odd_rest + 1)

def implementation (num: Int) : Int × Int := 
  let n := |num|.toNat
  let (even_count, odd_count) := count_even_odd_digits n
  (Int.ofNat even_count, Int.ofNat odd_count)

-- LLM HELPER
lemma count_even_odd_digits_zero : count_even_odd_digits 0 = (1, 0) := by
  rfl

-- LLM HELPER
lemma count_even_odd_digits_pos (n : Nat) (h : n > 0) :
  let digit := n % 10
  let (even_rest, odd_rest) := count_even_odd_digits (n / 10)
  count_even_odd_digits n = 
    if digit % 2 = 0 then (even_rest + 1, odd_rest)
    else (even_rest, odd_rest + 1) := by
  unfold count_even_odd_digits
  rw [if_neg (ne_of_gt h)]
  rfl

-- LLM HELPER
lemma nat_abs_div_ten (n : Nat) : 
  Int.natAbs (Int.ofNat (n / 10)) = n / 10 := by
  simp [Int.natAbs_of_nonneg, Int.ofNat_nonneg]

-- LLM HELPER
lemma toNat_of_natAbs_div_ten (n : Nat) :
  (Int.natAbs (Int.ofNat (n / 10))).toNat = n / 10 := by
  simp [Int.natAbs_of_nonneg, Int.ofNat_nonneg, Int.toNat_of_nonneg]

-- LLM HELPER
lemma even_iff_mod_two_eq_zero (n : Nat) : 
  Even (Int.ofNat n) ↔ n % 2 = 0 := by
  simp [Int.even_iff_two_dvd, Int.dvd_iff_mod_eq_zero, Int.mod_two_eq_zero_or_one]
  constructor
  · intro h
    cases' Nat.mod_two_eq_zero_or_one n with h0 h1
    · exact h0
    · simp [h1] at h
  · intro h
    simp [h]

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (n : Nat) :
  Odd (Int.ofNat n) ↔ n % 2 = 1 := by
  simp [Int.odd_iff_not_even, even_iff_mod_two_eq_zero]
  cases' Nat.mod_two_eq_zero_or_one n with h0 h1
  · simp [h0]
  · simp [h1]

theorem correctness
(num: Int)
: problem_spec implementation num := by
  rw [problem_spec]
  use implementation num
  constructor
  · rfl
  · simp [implementation]
    let numAbs := Int.natAbs num
    let numBy10 := numAbs / 10
    let (even_count, odd_count) := count_even_odd_digits numAbs
    let (even_count', odd_count') := count_even_odd_digits numBy10
    constructor
    · simp [nat_abs_div_ten, toNat_of_natAbs_div_ten]
      constructor
      · simp [Int.natAbs_of_nonneg, Int.ofNat_nonneg]
      · simp [Int.natAbs_of_nonneg, Int.ofNat_nonneg]
    · constructor
      · intro h_pos
        constructor
        · constructor
          · intro h_even
            simp [even_iff_mod_two_eq_zero] at h_even
            simp [Int.natAbs_of_nonneg h_pos] at h_even
            by_cases h_zero : numAbs = 0
            · simp [h_zero, count_even_odd_digits_zero]
              simp [Int.natAbs_of_nonneg h_pos] at h_zero
              rw [h_zero] at h_even
              simp at h_even
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [if_pos h_even]
              simp
          · intro h_eq
            simp [even_iff_mod_two_eq_zero]
            simp [Int.natAbs_of_nonneg h_pos]
            by_cases h_zero : numAbs = 0
            · simp [h_zero, count_even_odd_digits_zero] at h_eq
              simp [h_zero]
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              by_cases h_digit_even : numAbs % 10 % 2 = 0
              · rw [if_pos h_digit_even] at h_eq
                simp at h_eq
                exact h_digit_even
              · rw [if_neg h_digit_even] at h_eq
                simp at h_eq
                exfalso
                linarith
        · constructor
          · intro h_odd
            simp [odd_iff_mod_two_eq_one] at h_odd
            simp [Int.natAbs_of_nonneg h_pos] at h_odd
            by_cases h_zero : numAbs = 0
            · simp [h_zero] at h_odd
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [if_neg (fun h => by simp [h] at h_odd)]
              simp
          · intro h_eq
            simp [odd_iff_mod_two_eq_one]
            simp [Int.natAbs_of_nonneg h_pos]
            by_cases h_zero : numAbs = 0
            · simp [h_zero, count_even_odd_digits_zero] at h_eq
              simp [h_zero]
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              by_cases h_digit_even : numAbs % 10 % 2 = 0
              · rw [if_pos h_digit_even] at h_eq
                simp at h_eq
                exfalso
                linarith
              · rw [if_neg h_digit_even] at h_eq
                simp at h_eq
                cases' Nat.mod_two_eq_zero_or_one (numAbs % 10) with h0 h1
                · contradiction
                · exact h1
      · intro h_pos
        constructor
        · constructor
          · intro h_odd
            simp [odd_iff_mod_two_eq_one] at h_odd
            simp [Int.natAbs_of_nonneg h_pos] at h_odd
            by_cases h_zero : numAbs = 0
            · simp [h_zero] at h_odd
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [if_neg (fun h => by simp [h] at h_odd)]
              simp
          · intro h_eq
            simp [odd_iff_mod_two_eq_one]
            simp [Int.natAbs_of_nonneg h_pos]
            by_cases h_zero : numAbs = 0
            · simp [h_zero, count_even_odd_digits_zero] at h_eq
              simp [h_zero]
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              by_cases h_digit_even : numAbs % 10 % 2 = 0
              · rw [if_pos h_digit_even] at h_eq
                simp at h_eq
                exfalso
                linarith
              · rw [if_neg h_digit_even] at h_eq
                simp at h_eq
                cases' Nat.mod_two_eq_zero_or_one (numAbs % 10) with h0 h1
                · contradiction
                · exact h1
        · constructor
          · intro h_even
            simp [even_iff_mod_two_eq_zero] at h_even
            simp [Int.natAbs_of_nonneg h_pos] at h_even
            by_cases h_zero : numAbs = 0
            · simp [h_zero, count_even_odd_digits_zero]
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [count_even_odd_digits_pos numAbs h_pos_nat]
              simp
              rw [if_pos h_even]
              simp
          · intro h_eq
            simp [even_iff_mod_two_eq_zero]
            simp [Int.natAbs_of_nonneg h_pos]
            by_cases h_zero : numAbs = 0
            · simp [h_zero, count_even_odd_digits_zero] at h_eq
              simp [h_zero]
            · have h_pos_nat : numAbs > 0 := Nat.pos_of_ne_zero h_zero
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              rw [count_even_odd_digits_pos numAbs h_pos_nat] at h_eq
              simp at h_eq
              by_cases h_digit_even : numAbs % 10 % 2 = 0
              · rw [if_pos h_digit_even] at h_eq
                simp at h_eq
                exfalso
                linarith
              · rw [if_neg h_digit_even] at h_eq
                simp at h_eq
                cases' Nat.mod_two_eq_zero_or_one (numAbs % 10) with h0 h1
                · exact h0
                · contradiction