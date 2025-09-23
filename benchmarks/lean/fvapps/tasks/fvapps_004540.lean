-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hotpo (n : Nat) : Nat := sorry

theorem hotpo_terminates_at_one (n : Nat) (h : n > 0) : 
  hotpo n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hotpo_base_case :
  hotpo 1 = 0 := sorry

theorem hotpo_positive_for_greater_than_one (n : Nat) (h : n > 1) :
  hotpo n > 0 := sorry

theorem hotpo_even_numbers (n : Nat) (h : n > 0) (heven : n % 2 = 0) :
  hotpo n = hotpo (n / 2) + 1 := sorry
-- </vc-theorems>