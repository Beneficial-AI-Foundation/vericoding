-- <vc-preamble>
def abs (n : Int) : Int := 
  if n < 0 then -n else n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def clumsy (n : Nat) : Int := sorry

theorem clumsy_one :
  clumsy 1 = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem clumsy_two :
  clumsy 2 = 2 := sorry

theorem clumsy_bounds_larger (n : Nat) (h : n ≥ 3) (h2 : n ≤ 100) :
  n - 1 ≤ clumsy n ∧ clumsy n ≤ n + 3 := sorry

theorem clumsy_monotonic_small (n : Nat) (h : n ≤ 4) (h2 : n ≥ 1) :
  ∀ i, 1 ≤ i → i < n → clumsy i ≤ clumsy (i+1) := sorry
-- </vc-theorems>