-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def halving_sum (n : Nat) : Nat := sorry

/- For any positive n, halving_sum(n) is at least n -/
-- </vc-definitions>

-- <vc-theorems>
theorem halving_sum_lower_bound (n : Nat) (h : n > 0) : 
  halving_sum n ≥ n := sorry
-- </vc-theorems>