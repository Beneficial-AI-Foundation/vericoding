-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def integerBreak (n : Nat) : Nat := sorry

theorem integerBreak_positive (n : Nat) (h : n ≥ 2) : 
  integerBreak n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem integerBreak_geq_n (n : Nat) (h : n ≥ 4) :
  integerBreak n ≥ n := sorry

theorem integerBreak_2 :
  integerBreak 2 = 1 := sorry 

theorem integerBreak_3 :
  integerBreak 3 = 2 := sorry

theorem integerBreak_better_than_naive_split (n : Nat) (h : n ≥ 4) :
  integerBreak n ≥ 2^(n/2) * (if n % 2 = 0 then 1 else n % 2) := sorry
-- </vc-theorems>