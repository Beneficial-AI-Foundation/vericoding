-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : String := sorry

theorem solve_empty (s : String) :
  solve "" = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>