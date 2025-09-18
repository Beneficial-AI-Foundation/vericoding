-- <vc-preamble>
def calc_max_moves (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isqrt (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_max_moves_non_negative (x : Nat) :
  calc_max_moves x ≥ 0 :=
  sorry

theorem calc_max_moves_monotonic (x : Nat) :
  x > 0 → calc_max_moves x ≥ calc_max_moves (x-1) :=
  sorry
-- </vc-theorems>