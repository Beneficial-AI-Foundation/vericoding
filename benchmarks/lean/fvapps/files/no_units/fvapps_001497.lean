-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_remaining_stones (n1 n2 m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_remaining_stones_non_negative (n1 n2 m : Nat) :
  min_remaining_stones n1 n2 m ≥ 0 :=
  sorry

theorem min_remaining_stones_bounded (n1 n2 m : Nat) :
  min_remaining_stones n1 n2 m ≤ n1 + n2 :=
  sorry

theorem min_remaining_stones_zero_moves (n : Nat) :
  min_remaining_stones n n 0 = n + n :=
  sorry

theorem min_remaining_stones_symmetric (n1 n2 m : Nat) :
  min_remaining_stones n1 n2 m = min_remaining_stones n2 n1 m :=
  sorry

theorem min_remaining_stones_equal_piles_even (n m : Nat) (h : m > 0) :
  min_remaining_stones n n m % 2 = 0 :=
  sorry
-- </vc-theorems>