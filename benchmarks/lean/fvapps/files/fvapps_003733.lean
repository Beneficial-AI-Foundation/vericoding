-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hydrate (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hydrate_single_digit {n : Nat} (h : n ≤ 9) :
  hydrate s!"{n} drinks" =
    s!"{n} {if n = 1 then "glass" else "glasses"} of water" :=
sorry

theorem hydrate_multiple_digits {nums : List Nat} (h : ∀ n ∈ nums, n ≤ 9) :
  let sum := nums.foldl (· + ·) 0
  hydrate (String.intercalate " " (nums.map toString)) =
    s!"{sum} {if sum = 1 then "glass" else "glasses"} of water" :=
sorry

theorem hydrate_no_numbers {s : String}
  (h : ∀ c ∈ s.data, c = ' ' ∨ ('a' ≤ c ∧ c ≤ 'z')) :
  hydrate s = "0 glasses of water" :=
sorry

theorem hydrate_empty : hydrate "" = "0 glasses of water" :=
sorry
-- </vc-theorems>