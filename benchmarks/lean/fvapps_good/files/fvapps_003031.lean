-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Nat) : Nat := sorry

theorem solve_non_negative (a b : Nat) : 
  solve a b ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_empty_range (n : Nat) :
  solve n n = 0 := sorry 

theorem solve_consistent (a b : Nat) :
  solve (min a b) (max a b) = solve (min a b) (max a b) := sorry

theorem solve_subsegment (a b c : Nat) (h1: a ≤ b) (h2: b ≤ c) :
  solve a c ≥ solve a b + solve b c - 1 := sorry

theorem solve_monotonic_range (s e ext : Nat) (h: s ≤ e) :
  solve s e ≤ solve s (e + ext) := sorry
-- </vc-theorems>