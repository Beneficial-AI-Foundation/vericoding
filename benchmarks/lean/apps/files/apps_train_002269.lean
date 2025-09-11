-- <vc-preamble>
def solve_garland (n k : Nat) (s : String) : Nat := sorry

def is_valid_garland (n k : Nat) (s : String) : Bool := sorry

def count_zeros (s : String) : Nat := sorry 

def all_ones (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def all_zeros (s : String) : Bool := sorry

theorem solve_garland_nonnegative (n k : Nat) (s : String) :
  is_valid_garland n k s →
  solve_garland n k s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_garland_bounded_by_zeros (n k : Nat) (s : String) :
  is_valid_garland n k s →
  solve_garland n k s ≤ count_zeros s := sorry

theorem solve_garland_all_ones (n k : Nat) (s : String) :
  is_valid_garland n k s →
  all_ones s →
  solve_garland n k s = 0 := sorry

theorem solve_garland_all_zeros (n k : Nat) (s : String) :
  is_valid_garland n k s →
  all_zeros s →
  solve_garland n k s ≤ (n + k - 1) / k := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_garland 9 2 "010001010"

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_garland 9 3 "111100000"

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_garland 1 1 "0"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded