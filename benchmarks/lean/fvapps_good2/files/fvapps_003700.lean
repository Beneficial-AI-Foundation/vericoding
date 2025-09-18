-- <vc-preamble>
def sumMultiples (n : Nat) : Int :=
  (List.range n).map Int.ofNat
  |>.filter (fun x => x % 3 = 0 ∨ x % 5 = 0)
  |>.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_nonnegative (n : Int) :
  solution n ≥ 0 ∧ (n ≤ 0 → solution n = 0) :=
sorry

theorem multiples_property {n : Nat} :
  0 < n →
  solution (Int.ofNat n) = sumMultiples n :=
sorry

theorem result_smaller_than_input_squared {n : Int} :
  n > 0 → solution n < n * n :=
sorry

theorem negative_inputs :
  ∀ n : Int, n < 0 → solution n = 0 :=
sorry
-- </vc-theorems>