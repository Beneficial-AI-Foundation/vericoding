-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_circle_arrangement (n : Nat) : String :=
  sorry

def validate_arrangement (n : Nat) (result : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_string {n : Nat} :
  ∃ s : String, solve_circle_arrangement n = s
  :=
sorry

theorem solve_starts_with_yes_or_is_no {n : Nat} :
  let result := solve_circle_arrangement n
  result.startsWith "YES\n" ∨ result = "NO"
  :=
sorry

theorem result_validates {n : Nat} :
  validate_arrangement n (solve_circle_arrangement n) = true
  :=
sorry

theorem validates_checks_length {n : Nat} {result : String} :
  result ≠ "NO" → validate_arrangement n result = true →
  ∃ nums : List Nat,

    nums.length = 2 * n
  :=
sorry

theorem validates_checks_unique_nums {n : Nat} {result : String} :
  result ≠ "NO" → validate_arrangement n result = true →
  ∃ nums : List Nat,

    nums = List.range (2 * n)
  :=
sorry

theorem validates_checks_consecutive_sums {n : Nat} {result : String} :
  result ≠ "NO" → validate_arrangement n result = true →
  ∃ nums : List Nat,
    let doubled := nums ++ nums
    ∃ sums : List Nat,
      ∃ maxSum minSum : Nat,
        maxSum - minSum ≤ 1
  :=
sorry
-- </vc-theorems>