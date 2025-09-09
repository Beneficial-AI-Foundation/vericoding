-- <vc-helpers>
-- </vc-helpers>

def solve (s : String) : String := sorry

theorem solve_empty (s : String) :
  solve "" = "" := sorry

theorem solve_add_commutes (a b : String) :
  solve "a+b" = "b+a" := sorry

theorem solve_sub_commutes (a b : String) :
  solve "a-b" = "b-a" := sorry

theorem solve_mul_commutes (a b : String) :
  solve "a*b" = "b*a" := sorry

theorem solve_div_commutes (a b : String) :
  solve "a/b" = "b/a" := sorry

theorem solve_add_sub_commutes (a b c : String) :
  solve "a+b-c" = "c-b+a" := sorry

theorem solve_mul_div_commutes (x y z : String) :
  solve "x*y/z" = "z/y*x" := sorry

theorem solve_add_mul_commutes (a b c : String) :
  solve "a+b*c" = "c*b+a" := sorry

theorem solve_div_sub_commutes (x y z : String) :
  solve "x/y-z" = "z-y/x" := sorry

/-
info: 'y/b*100'
-/
-- #guard_msgs in
-- #eval solve "100*b/y"

/-
info: '30*d/c-b+a'
-/
-- #guard_msgs in
-- #eval solve "a+b-c/d*30"

/-
info: '50+c/b*a'
-/
-- #guard_msgs in
-- #eval solve "a*b/c+50"

-- Apps difficulty: introductory
-- Assurance level: unguarded