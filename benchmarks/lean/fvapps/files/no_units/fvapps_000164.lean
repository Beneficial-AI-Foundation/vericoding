-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def super_egg_drop (K N : Nat) : Nat := sorry

theorem super_egg_drop_positive (K N : Nat) (h1 : K > 0) (h2 : N > 0) :
  super_egg_drop K N > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem super_egg_drop_upper_bound (K N : Nat) (h1 : K > 0) (h2 : N > 0) :
  super_egg_drop K N ≤ N := sorry

theorem super_egg_drop_one_egg (N : Nat) (h : N > 0) :
  super_egg_drop 1 N = N := sorry

theorem super_egg_drop_monotonic_K (K N : Nat) (h1 : K > 1) (h2 : N > 0) :
  super_egg_drop K N ≤ super_egg_drop (K-1) N := sorry

theorem super_egg_drop_min_case :
  super_egg_drop 1 1 = 1 := sorry

theorem super_egg_drop_linear_search :
  super_egg_drop 1 5 = 5 := sorry

theorem super_egg_drop_multiple_eggs_efficient :
  super_egg_drop 2 10 < 10 := sorry
-- </vc-theorems>