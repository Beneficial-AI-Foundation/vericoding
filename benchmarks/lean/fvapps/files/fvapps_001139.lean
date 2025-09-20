-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_party_guests (n : Nat) (friends : List Nat) : Nat := sorry

theorem solve_party_guests_non_negative (n : Nat) (friends : List Nat) :
  n > 0 → solve_party_guests n friends ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_party_guests_monotonic (n : Nat) (friends : List Nat) (a : Nat) :
  n > 0 → solve_party_guests (n + 1) (friends ++ [a]) ≥ solve_party_guests n friends := sorry
-- </vc-theorems>