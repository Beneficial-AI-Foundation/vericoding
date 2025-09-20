-- <vc-preamble>
def count_val (n : Nat) (xs : List Nat) : Nat :=
  List.length (List.filter (· = n) xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_seven (arr : List Nat) : Bool := sorry

def hungry_seven (arr : List Nat) : List Nat :=
sorry

def is_valid_result (input : List Nat) (result : List Nat) : Bool :=
sorry

def has_89_pattern (arr : List Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hungry_seven_properties (arr : List Nat)
  (h1 : ∀ x ∈ arr, x = 7 ∨ x = 8 ∨ x = 9)
  : let result := hungry_seven arr

    (result.length = arr.length) ∧

    (∀ x ∈ result, x = 7 ∨ x = 8 ∨ x = 9) ∧

    (count_val 7 arr = count_val 7 result) ∧
    (count_val 8 arr = count_val 8 result) ∧
    (count_val 9 arr = count_val 9 result) ∧

    (hungry_seven result = result) ∧

    ((!has_seven arr ∨ !has_89_pattern arr) → result = arr) :=
sorry

theorem no_seven_before_89_pattern (arr : List Nat)
  (h1 : arr.length ≥ 2)
  (h2 : ∀ x ∈ arr, x ≥ 7 ∧ x ≤ 9) :
  let result := hungry_seven arr
  ∀ i < result.length - 1,
    result[i]? = some 7 →
    ¬(result[i+1]? = some 8 ∧ result[i+2]? = some 9) :=
sorry
-- </vc-theorems>