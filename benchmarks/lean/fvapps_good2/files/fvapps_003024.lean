-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits_of (n : Nat) : List Nat :=
sorry

def digit_sequence_of_powers (n : Nat) : List Nat :=
sorry

def last_digit_to_appear (n : Nat) : Option Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_single_digit {n d : Nat} (h : n ≥ 2)
  (res : last_digit_to_appear n = some d) :
  0 ≤ d ∧ d ≤ 9 :=
sorry

theorem appears_last {n d : Nat} (h : n ≥ 2)
  (res : last_digit_to_appear n = some d)
  (digits : List Nat)
  (nonempty : digits ≠ [])
  (valid_digits : ∀ x, x ∈ digits → x ≤ 9)
  (is_sequence : digits = digit_sequence_of_powers n)
  (h_len : digits.length > 0) :
  d = digits[digits.length - 1]'(Nat.sub_lt h_len (by exact Nat.zero_lt_one)) :=
sorry

theorem none_result_characterization {n : Nat} (h : n ≥ 2)
  (res : last_digit_to_appear n = none) :
  (∀ k : Nat, k > 1 → digits_of (n^k) = digits_of n) ∨
  (∃ x : Nat, x ≤ 9 ∧ ∀ k : Nat, k ≤ 100 → x ∉ digits_of (n^k)) :=
sorry
-- </vc-theorems>