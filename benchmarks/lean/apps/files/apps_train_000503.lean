-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compare_and_calc (n1 n2 : Int) : Int := sorry

theorem compare_and_calc_spec (n1 n2 : Int) : 
  compare_and_calc n1 n2 = if n1 > n2 then n1 - n2 else n1 + n2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compare_and_calc_same (n : Int) : 
  compare_and_calc n n = n + n := sorry

/-
info: 54
-/
-- #guard_msgs in
-- #eval compare_and_calc 82 28

/-
info: 30
-/
-- #guard_msgs in
-- #eval compare_and_calc 10 20

/-
info: 0
-/
-- #guard_msgs in
-- #eval compare_and_calc 0 0
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible