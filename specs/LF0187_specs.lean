-- <vc-preamble>
def countValidDigits (digits : List String) (n : Nat) : Nat :=
  (digits.filter (fun d => d.toNat?.getD 0 ≤ n)).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def atMostNGivenDigitSet (digits : List String) (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_nonnegative {digits : List String} {n : Nat} :
  0 ≤ atMostNGivenDigitSet digits n :=
sorry

theorem result_within_max_possible {digits : List String} {n : Nat} :
  let max_len := toString n |>.length
  atMostNGivenDigitSet digits n ≤ (digits.length ^ max_len) :=
sorry

theorem single_digit_result {digits : List String} {n : Nat} :
  n < 10 →
  atMostNGivenDigitSet digits n = countValidDigits digits n :=
sorry

theorem empty_digit_list_fails (n : Nat) :
  atMostNGivenDigitSet [] n = 0 :=
sorry

theorem single_digit_basic_cases_1 :
  atMostNGivenDigitSet ["1"] 1 = 1 :=
sorry

theorem single_digit_basic_cases_2 :
  atMostNGivenDigitSet ["9"] 10 = 1 :=
sorry
-- </vc-theorems>