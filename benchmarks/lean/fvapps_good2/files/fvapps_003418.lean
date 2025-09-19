-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_dig (n: Nat) : Nat :=
sorry

def is_happy (n: Nat) : Bool :=
sorry

def performant_numbers (n: Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_dig_nonnegative (n: Nat) :
  sum_dig n ≥ 0 :=
sorry

theorem sum_dig_upper_bound (n: Nat) (k: Nat) :
  sum_dig n ≤ k * 81 :=
sorry

theorem is_happy_bool_result (n: Nat) :
  is_happy n = true ∨ is_happy n = false :=
sorry

theorem known_happy_numbers (n: Nat) :
  n = 1 ∨ n = 7 ∨ n = 10 ∨ n = 13 ∨ n = 19 ∨ n = 23 ∨ n = 28 ∨ n = 31 →
  is_happy n = true :=
sorry

theorem known_unhappy_numbers (n: Nat) :
  n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9 →
  is_happy n = false :=
sorry

theorem performant_numbers_sorted (n: Nat) :
  let result := performant_numbers n
  ∀ i < result.length - 1,
    result[i]! ≤ result[i+1]! :=
sorry

theorem performant_numbers_bounded (n: Nat) :
  ∀ x ∈ performant_numbers n, x ≤ n :=
sorry

theorem performant_numbers_contains_happy (n: Nat) :
  ∀ x ∈ [1, 7, 10, 13, 19, 23, 28, 31],
    x ≤ n → x ∈ performant_numbers n :=
sorry
-- </vc-theorems>