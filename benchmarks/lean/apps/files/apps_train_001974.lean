-- <vc-helpers>
-- </vc-helpers>

def solve_group_division (n a b c d : Nat) : Nat := sorry

theorem group_division_non_negative (n a b c d : Nat)
  (h1 : b ≥ a)
  (h2 : d ≥ c) 
  (h3 : n ≥ c * a) :
  solve_group_division n a b c d ≥ 0 := sorry

theorem group_division_mod_bound (n a b c d : Nat)
  (h1 : b ≥ a)
  (h2 : d ≥ c)
  (h3 : n ≥ c * a) :
  solve_group_division n a b c d < 10^9 + 7 := sorry

theorem impossible_cases (n a : Nat)
  (h : n < a) :
  solve_group_division n a a 1 1 = 0 := sorry

-- Apps difficulty: competition
-- Assurance level: guarded