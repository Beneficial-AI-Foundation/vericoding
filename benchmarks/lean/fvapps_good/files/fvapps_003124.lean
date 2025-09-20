-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def enough (cap on wait : Nat) : Nat := sorry

theorem enough_nonneg (cap on wait : Nat) :
  cap > 0 → enough cap on wait ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem enough_fits (cap on wait : Nat) :
  cap > 0 → on + wait ≤ cap → enough cap on wait = 0 := sorry
-- </vc-theorems>