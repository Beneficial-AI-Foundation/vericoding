-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def div_num (n : Nat) : Nat := sorry

theorem div_num_positive (n : Nat) (h : n > 0) : div_num n ≥ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem div_num_perfect_squares 
  (n : Nat) 
  (h : n > 0) : 
  div_num (n * n) % 2 = 1 := sorry

theorem div_num_small_cases_1 : div_num 1 = 1 := sorry

theorem div_num_small_cases_2 : div_num 2 = 2 := sorry 

theorem div_num_small_cases_4 : div_num 4 = 3 := sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval find_min_num 6

/-
info: 48
-/
-- #guard_msgs in
-- #eval find_min_num 10

/-
info: 60
-/
-- #guard_msgs in
-- #eval find_min_num 12
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded