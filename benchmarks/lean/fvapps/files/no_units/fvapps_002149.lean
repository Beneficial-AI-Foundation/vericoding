-- <vc-preamble>
def abs (n : Int) : Int := 
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_wabbit (x1 y1 x2 y2 : Int) : Int := sorry

theorem wabbit_nonnegative (x1 y1 x2 y2 : Int) :
  solve_wabbit x1 y1 x2 y2 ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wabbit_same_point (x y : Int) :
  solve_wabbit x y x y = 0 := sorry

theorem wabbit_symmetry (x1 y1 x2 y2 : Int) :
  solve_wabbit x1 y1 x2 y2 = solve_wabbit x2 y2 x1 y1 := sorry
-- </vc-theorems>