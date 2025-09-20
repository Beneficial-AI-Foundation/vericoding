-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrangeCoins (n: Nat) : Nat := sorry

theorem arrange_coins_valid_input (n: Nat) (h: n ≥ 1) :
  let result := arrangeCoins n
  result ≥ 1 ∧ 
  result * (result + 1) / 2 ≤ n ∧
  (result + 1) * (result + 2) / 2 > n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arrange_coins_monotonic (n: Nat) (h: n ≥ 1) :
  arrangeCoins (n + 1) ≥ arrangeCoins n := sorry
-- </vc-theorems>