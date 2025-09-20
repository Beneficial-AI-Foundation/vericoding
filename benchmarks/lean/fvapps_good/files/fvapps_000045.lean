-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_nice_staircases (n : Nat) : Nat := sorry

theorem count_nice_staircases_positive (n : Nat) (h : n > 0):
  count_nice_staircases n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_nice_staircases_bounded (n : Nat):
  count_nice_staircases n ≤ n := sorry

theorem count_nice_staircases_deterministic (n : Nat):
  count_nice_staircases n = count_nice_staircases n := sorry

theorem count_nice_staircases_monotonic (n : Nat) (h : n > 1):
  count_nice_staircases n ≥ count_nice_staircases (n-1) := sorry
-- </vc-theorems>