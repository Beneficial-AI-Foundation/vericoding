-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def racecar (target : Nat) : Nat := sorry

theorem racecar_output_positive (target : Nat) : 
  target > 0 → racecar target > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem racecar_growth (target : Nat) :
  target > 0 → racecar target ≤ 4 * target.log2 := sorry

theorem racecar_optimal_for_power2minus1 (target : Nat) :
  target > 0 → 
  (∃ k : Nat, target + 1 = 2^k) →
  racecar target = (target + 1).log2 - 1 := sorry

theorem racecar_consistent (target : Nat) :
  target > 0 →
  racecar target = racecar target := sorry
-- </vc-theorems>