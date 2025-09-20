-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_garland (n k : Nat) (s : String) : Nat :=
sorry

def is_valid_garland (n k : Nat) (s : String) : Bool :=
sorry

def count_zeros (s : String) : Nat :=
sorry

def all_ones (s : String) : Bool :=
sorry

def all_zeros (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_garland_nonnegative (n k : Nat) (s : String) :
  is_valid_garland n k s →
  solve_garland n k s ≥ 0 :=
sorry

theorem solve_garland_bounded_by_zeros (n k : Nat) (s : String) :
  is_valid_garland n k s →
  solve_garland n k s ≤ count_zeros s :=
sorry

theorem solve_garland_all_ones (n k : Nat) (s : String) :
  is_valid_garland n k s →
  all_ones s →
  solve_garland n k s = 0 :=
sorry

theorem solve_garland_all_zeros (n k : Nat) (s : String) :
  is_valid_garland n k s →
  all_zeros s →
  solve_garland n k s ≤ (n + k - 1) / k :=
sorry
-- </vc-theorems>