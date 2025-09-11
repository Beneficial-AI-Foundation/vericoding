-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_operations (s : String) : Nat := sorry

theorem result_positive (s : String) (h : s.length > 0) : 
  solve_string_operations s > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounded (s : String) (h : s.length > 0) :
  solve_string_operations s ≤ s.length := sorry

theorem single_char_result (s : String) (h : s.length = 1) :
  solve_string_operations s = 1 := sorry

theorem append_zero_bound (s : String) (h : s.length > 0) :
  (solve_string_operations (s ++ "0") - solve_string_operations s) ≤ 1 ∧ 
  (solve_string_operations s - solve_string_operations (s ++ "0")) ≤ 1 := sorry

theorem append_one_bound (s : String) (h : s.length > 0) :  
  (solve_string_operations (s ++ "1") - solve_string_operations s) ≤ 1 ∧
  (solve_string_operations s - solve_string_operations (s ++ "1")) ≤ 1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_string_operations "111010"

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_string_operations "0"

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_string_operations "101010"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible