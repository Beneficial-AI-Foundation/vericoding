-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def f (x : α) : Option Nat := sorry

/- For positive integers, f(n) equals the sum of numbers from 1 to n -/
-- </vc-definitions>

-- <vc-theorems>
theorem positive_integers_sum {n : Nat} (h : n > 0) : 
  f n = some (n * (n + 1) / 2) := sorry
-- </vc-theorems>